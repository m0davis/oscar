
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
record Alphabet
```

### Parameterisation

`Γ` is intended to represent a context as viewed from the outside of the represented term, whereas `Δ` is similar but meant to be as viewed from the inside (like a DeBruijn index). In the toy model I have in mind, `Γ` would be a `Nat` representing the number of free variables in the term, and `Δ` would also be a `Nat` representing the number of variables available in the context at a given place within the term (that is, the bound variables).

```agda
  {Γ Δ : Set}
```

`X` is a family of terms, with members distinguished by the number of free variables, and `V` is a family of bound variables, with members distinguished by the size of the context.

```agda
  (X : Γ → Set)
  (V : Δ → Set)
```

The term-like language I model here has one constant symbol carrying a value as represented by `K`.

```agda
  (K : Set)
```

`γ₀` represents a nullary number of free variabes, so `X γ₀` is a closed term.

```agda
  (γ₀ : Γ)
```

`r` represents the expansion of a context by additional bound variables.

```agda
  (r : Γ → Δ → Γ)
```

```agda
  : Set where
```

### Manifestation

```agda
  field
```

The model is populated by a `variable` and `constant` symbol, as well as a number of symbols for defined `functions`.

```agda
    variable : ∀ {δ} → V δ → ∀ {γ} ⦃ _ : γ ≡ r γ₀ δ ⦄ → X γ
    constant : ∀ {γ} → K → X γ
    {#} : Nat
    functions : Vec (Recon X r) #
```

The model semantics demands that the terms be representable in a certain way according to the given symbols.

```agda
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
  myAlphabet : Alphabet MyLanguage Fin Nat 0 (flip _+_)
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

Such conversions are inverses of one another, and so characterise an isomorphism. Here is a messy half-proof.

```agda
    transportation-eq :
      ∀ {a b} {A : Set a} (B : A → Set b) {x y} → (eq eq' : x ≡ y) → (bx : B x)
      → transport B eq bx ≡ transport B eq' bx
    transportation-eq B refl refl bx = refl

    transportation-drop : ∀ {a b} {A : Set a} (B : A → Set b) {x} → (eq : x ≡ x) → (bx : B x) → transport B eq bx ≡ bx
    transportation-drop B refl bx = refl

    varfact : ∀ {δ} → (vv : Fin δ) → ∀ {γ} ⦃ eq : γ ≡ _+_ δ 0 ⦄ → Σ _ λ z → variable vv ⦃ eq ⦄ ≡ υ z
    varfact vv ⦃ eq ⦄ with variable vv ⦃ eq ⦄ | graphAt (λ z → variable z ⦃ eq ⦄) vv
    varfact vv {{eq = refl}} | .(υ (transport Fin auto vv)) | ingraph refl = transport Fin auto vv , refl

    inj-variable : ∀ {δ} → (vv : Fin δ) → ∀ {γ} ⦃ eq : γ ≡ _+_ δ 0 ⦄ → variable vv ⦃ eq ⦄ ≡ υ (transport Fin (trans auto (sym eq)) vv)
    inj-variable vv ⦃ eq ⦄ with variable vv ⦃ eq ⦄ | graphAt (λ z → variable z ⦃ eq ⦄) vv
    inj-variable vv {{eq = refl}} | .(υ (transport Fin auto vv)) | ingraph refl = cong υ (transportation-eq Fin auto (trans auto refl) vv)

    v2v : ∀ N (x : Fin N) (an : _≡_ {lzero} {Nat} N (N + 0)) →
          _≡_ {lzero} {MyLanguage N} (variable {N} x {N} {{an}}) (υ x)
    v2v N x an with mkInstance an | transport (λ v → N ≡ v) an refl | graphAt (transport (λ v → N ≡ v) an) refl | variable {N} x {N} {{an}} | graphAt (λ v → variable {N} x {N} {{v}}) an | varfact x ⦃ an ⦄
    v2v N x' an | ! {{x = x}} | .(transport {lzero} {lzero} {Nat} (_≡_ {lzero} {Nat} N) {N} {N + 0} an refl) | ingraph refl | .(myAlphabet .Alphabet.variable {N} x' {N} {{an}}) | ingraph refl | fst₁ , snd₁ rewrite snd₁ = trans (sym snd₁) (trans (inj-variable x' {{an}}) (cong υ (transportation-drop Fin (trans auto (sym an)) x')))

    language-to-language : ∀ {N} (l : MyLanguage N) → alphabet-to-language (language-to-alphabet l) ≡ l
    language-to-language l with language-to-alphabet l | graphAt language-to-alphabet l
    language-to-language {N} (υ x) | (υ {δ} {{.auto}} .x) | ingraph refl with auto ofType N ≡ N + zero | graphAt (λ n → auto ofType n ≡ n + zero) N
    language-to-language {N} (υ x) | (υ {δ} {{.auto}} .x) | ingraph refl | an | ingraph gat = v2v N x an
    language-to-language {N} (κ _) | _ | ingraph refl = refl
    language-to-language {N} (ΠF l₁ l₂) | _ | ingraph refl = cong₂ ΠF (language-to-language l₁) (language-to-language l₂)
    language-to-language {N} (ΠI l₁) | _ | ingraph refl = cong ΠI (language-to-language l₁)
    language-to-language {N} (ΠE l₁ l₂) | _ | ingraph refl = cong₂ ΠE (language-to-language l₁) (language-to-language l₂)
```

# Further research

The (messy, half) proof of isomorphism should be cleaned-up and completed. Beyond that, `Alphabet` could be extended to demand that there is an encoding, similar to `language-to-alphabet`, of the terms to be modeled into the modeled `Alphabet.Term`, and that such a thing is an inverse of `Alphabet.reifyTerm`. (Because Agda does not, as of version 2.6.0-9496f75, allow `field` after `data` declarations within a `record`, such an extension would require a separate `record` type.)

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
      alphabet : Alphabet X V K γ₀ r
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
