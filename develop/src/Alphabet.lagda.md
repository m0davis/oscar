
(There is some unsolved business herein.)

```agda
{-# OPTIONS --allow-unsolved-metas #-}
```
# Alphabet: models of term-like languages

```agda
module Alphabet where
```

I characterise term-like languages and show that a certain model is isomorphic to a particular toy language. The resulting machinery turns out to be insufficient to describe weakening or substitution.

```agda
open import Prelude
open import Tactic.Nat
```

## Helper structures

`IVec` is a cons-list of witnesses to members of a type family, indexed by a length-indexed cons-list of the family membership indices.

```
data IVec {I : Set} (X : I → Set) : ∀ {#} → Vec I # → Set where
  [] : IVec X []
  _∷_ : ∀ {i} → X i
      → ∀ {#is} {is : Vec I #is} → IVec X is
      → IVec X (i ∷ is)
```

`Recon` represents a recursive constructor.

```agda
record Recon {I J : Set} (X : I → Set) (r : I → J → I) : Set where
  constructor _▶_
  field
    {#} : Nat -- number of arguments
    js : Vec J # -- recursive bindings for each argument position
    con : ∀ {i}
        → IVec (X ∘ r i) js -- evaluated arguments
        → X i -- constructed
```

## Main model

`Alphabet` describes the symbol-set that makes up a term-like language. Such a language must feature a symbol for variables and for constants, as well as some number of defined functions.

```agda
record Alphabet {Γ Δ : Set}
                (X : Γ → Set) -- terms, indexed by a context (an environment, as viewed from the outside)
                (V : Δ → Set) -- variables, indexed as DeBruijn would have (an environment, as viewed from the inside)
                (γ₀ : Γ) -- nullary context
                (K : Set)
                (r : Γ → Δ → Γ) -- addition to a context
       : Set where
  field
    variable : ∀ {δ} → V δ → ∀ {γ} ⦃ _ : γ ≡ r γ₀ δ ⦄ → X γ
    constant : ∀ {γ} → K → X γ
    {#} : Nat
    functions : Vec (Recon X r) #

  data Term (γ : Γ) : Set
  data Function (γ : Γ) : ∀ {#} → Vec Δ # → Set

  data Term (γ : Γ) where
    υ : ∀ {δ} ⦃ _ : γ ≡ r γ₀ δ ⦄ → V δ → Term γ
    κ : K → Term γ
    φ : (f : Fin #)
      → Function γ (Recon.js (indexVec functions f))
      → Term γ

  data Function (γ : Γ) where
    [] : Function γ []
    _∷_ : ∀ {δ} → Term (r γ δ)
        → ∀ {#δs} {δs : Vec Δ #δs} → Function γ δs
        → Function γ (δ ∷ δs)

  reifyTerm : ∀ {γ} → Term γ → X γ
  reifyFunction : ∀ {γ} {#δs} {δs : Vec Δ #δs}
             → Function γ δs
             → IVec (X ∘ r γ) δs

  reifyTerm (υ v) = variable v
  reifyTerm (κ k) = constant k
  reifyTerm (φ f Φ) = Recon.con (indexVec functions f) (reifyFunction Φ)
  reifyFunction {δs = []} _ = []
  reifyFunction {δs = δ ∷ δs} (τ ∷ Φ) = reifyTerm τ ∷ reifyFunction Φ
```

# Results

```agda
private
```

Thus far, the above is enough to model a target language such as the following.

```agda
  data MyLanguage (N : Nat) : Set where
    υ : Fin N → MyLanguage N
    κ : Nat → MyLanguage N
    ΠF : MyLanguage N → MyLanguage (suc N) → MyLanguage N
    ΠI : MyLanguage (suc N) → MyLanguage N
    ΠE : MyLanguage N → MyLanguage N → MyLanguage N
```

Here is a model of `MyLanguage`:

```agda
  myAlphabet : Alphabet MyLanguage Fin 0 Nat (flip _+_)
  myAlphabet .Alphabet.variable v ⦃ refl ⦄ = υ (transport Fin auto v)
  myAlphabet .Alphabet.constant k = κ k
  myAlphabet .Alphabet.# = 3
  myAlphabet .Alphabet.functions =
    ((0 ∷ 1 ∷ []) ▶ λ { (x₁ ∷ x₂ ∷ []) → ΠF x₁ x₂}) ∷
    ((1 ∷     []) ▶ λ { (x₁ ∷      []) → ΠI x₁   }) ∷
    ((0 ∷ 0 ∷ []) ▶ λ { (x₁ ∷ x₂ ∷ []) → ΠE x₁ x₂}) ∷
    []
```

In the model, I can construct arbitrary statements of `MyLanguage`, and, in `MyLanguage`, I can construct arbitrary modeled `Alphabet.Term`s.

```agda
  module _ where
    open Alphabet myAlphabet

    language-to-alphabet : ∀ {N} → MyLanguage N → Term N
    language-to-alphabet (υ v) = υ ⦃ auto ⦄ v
    language-to-alphabet (κ k) = κ k
    language-to-alphabet (ΠF x₁ x₂) = φ 0 $ language-to-alphabet x₁ ∷ language-to-alphabet x₂ ∷ []
    language-to-alphabet (ΠI x₁   ) = φ 1 $ language-to-alphabet x₁ ∷ []
    language-to-alphabet (ΠE x₁ x₂) = φ 2 $ language-to-alphabet x₁ ∷ language-to-alphabet x₂ ∷ []

    alphabet-to-language : ∀ {N} → Term N → MyLanguage N
    alphabet-to-language = reifyTerm
```

Such conversions are inverses of one another, and so characterise an isomorphism. The proof is a little tricky and I have not finished it. But here is an unfinished half-proof which suggests that a full proof is possible.

```agda
    language-to-language : ∀ {N} (l : MyLanguage N)
                             (a : Term N) → language-to-alphabet l ≡ a →
                             (l' : MyLanguage N) → alphabet-to-language a ≡ l' →
                             l' ≡ l
    language-to-language {.1} (υ (zero {zero})) .(υ zero) refl .(υ zero) refl = refl
    language-to-language (υ (zero {suc zero})) _ refl _ refl = refl
    language-to-language (υ (zero {suc (suc n)})) _ refl _ refl = {!!}
    language-to-language (υ (suc {.1} (zero {zero}))) _ refl _ refl = refl
    language-to-language (υ (suc {.(suc (suc n))} (zero {suc n}))) _ refl _ refl = {!!}
    language-to-language (υ (suc {.(suc _)} (suc x))) _ refl _ refl = {!!}
    language-to-language (κ x) .(κ x) refl .(κ x) refl = refl
    language-to-language (ΠF l l₁) _ refl _ refl = cong₂ ΠF (language-to-language l _ refl _ refl) (language-to-language l₁ _ refl _ refl)
    language-to-language (ΠI l) _ refl _ refl = cong ΠI (language-to-language l _ refl _ refl)
    language-to-language (ΠE l l₁) _ refl _ refl = cong₂ ΠE (language-to-language l _ refl _ refl) (language-to-language l₁ _ refl _ refl)
```

# Further research

The proof of isomorphism is straightforward and should be completed. Beyond that, `Alphabet` could be extended to demand that there is an encoding, similar to `language-to-alphabet`, of the terms to be modeled into the modeled `Alphabet.Term`, and that such a thing is an inverse of `Alphabet.reifyTerm`. (Because Agda does not, as of version 2.6.0-9496f75, allow `field` after `data` declarations within a `record`, such an extension would require a separate `record` type.)

The parameterisation `γ₀ : Γ` and `r : Γ → Δ → Γ` feels ad-hoc to me. `γ₀` is only used in combination with `r`, so a stronger parameterisation would discard `γ₀` but include `r` and `r₀ : Δ → Γ`, where `r₀ = r γ₀`.

The concepts of contextual weakening or variable-for-term substitution are not expressible from an `Alphabet` because, at least in part, there is nothing in its type signature that allows one to characterise a position in the context from which to weaken or at which to substitute, nor is there a way to characterise the contextual reduction as a result of substitution.

In the case of `MyLanguage`, such functions would be described as follows:

```agda
  postulate
    weakenMyLanguage
      : (by : Nat)          -- weaken the context by this number of elements
      → ∀ {N} → Fin (suc N) -- starting from this position
      → MyLanguage N        -- of this statement
      → MyLanguage (by + N)
    substituteMyLanguage
      : ∀ {N} → Fin (suc N) -- substitute, at this position,
      → MyLanguage N        -- this replacement statement
      → MyLanguage (suc N)  -- within this statement
      → MyLanguage N
```

A solution might include the addition of a position type, `Ψ : Γ → Set`, and a contextual expansion function, `↑ : Γ → Γ`. In the below, I add those and discover what else I might need.

```agda
  record SyntacticAlphabet
    {Γ Δ : Set}
    (X : Γ → Set)
    (V : Δ → Set)
    (γ₀ : Γ)
    (K : Set)
    (r : Γ → Δ → Γ)
    (Ψ : Γ → Set)
    (↑ : Γ → Γ)
    : Set
    where
    field
      alphabet : Alphabet X V γ₀ K r
    open Alphabet alphabet

    weakenTerm
      : (δ : Δ)
      → ∀ {γ} → Ψ γ
      → Term γ
      → Term (r γ δ)
    weakenTerm δ {γ} ψ (υ {δ'} ⦃ refl ⦄ v) = υ {δ = {!weakenΔ δ' δ {-ofType Δ-}!}} ⦃ {!refl {-ofType r (r γ₀ δ') δ ≡ r γ₀ (weakenΔ δ' δ)-}!} ⦄ {!weakenV δ ψ v {-ofType V (weakenΔ δ' δ)-}!}
    weakenTerm δ ψ (κ k) = κ k
    weakenTerm δ {γ} ψ (φ f Φ) = φ f {!weakenFunction δ ψ (indexVec functions f .Recon.js) Φ!}

    substituteTerm
      : ∀ {γ} → Ψ γ
      → Term γ
      → Term (↑ γ)
      → Term γ
    substituteTerm {γ} ψ ρ τ@(υ {δ'} v) = {!substituteV ψ ρ v!} -- υ {δ = {!substituteΔ!}} ⦃ {!refl!} ⦄ {!substituteV ψ ρ v!}
    substituteTerm ψ ρ (κ k) = κ k
    substituteTerm ψ ρ (φ f Φ) = φ f {!substituteFunction ψ ρ (indexVec functions f .Recon.js) Φ!}
```
