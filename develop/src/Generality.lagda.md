
# Generality: being as general as possible, but not any more so (h/t Einstein)

```agda
module Generality where
```

```agda
open import Prelude
open import Tactic.Nat
```

I had defined the following system and remarked:

> The parameterisation `γ₀ : Γ` and `r : Γ → Δ → Γ` feels ad-hoc to me. `γ₀` is only used in combination with `r`, so a stronger parameterisation would discard `γ₀` but include `r` and `r₀ : Δ → Γ`, where `r₀ = r γ₀`.

```agda
module Weaker where

  data IVec {I : Set} (X : I → Set) : ∀ {#} → Vec I # → Set where
    [] : IVec X []
    _∷_ : ∀ {i} → X i
        → ∀ {#is} {is : Vec I #is} → IVec X is
        → IVec X (i ∷ is)

  record Recon {I J : Set} (X : I → Set) (r : I → J → I) : Set where
    constructor _▶_
    field
      {#} : Nat
      js : Vec J #
      con : ∀ {i}
          → IVec (X ∘ r i) js
          → X i

  record Alphabet
    {Γ Δ : Set}
    (X : Γ → Set)
    (V : Δ → Set)
    (K : Set)
    (γ₀ : Γ)
    (r : Γ → Δ → Γ)
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

Heeding the above advice yields:

```agda
module Stronger where

  data IVec {I : Set} (X : I → Set) : ∀ {#} → Vec I # → Set where
    [] : IVec X []
    _∷_ : ∀ {i} → X i
        → ∀ {#is} {is : Vec I #is} → IVec X is
        → IVec X (i ∷ is)

  record Recon {I J : Set} (X : I → Set) (r : I → J → I) : Set where
    constructor _▶_
    field
      {#} : Nat
      js : Vec J #
      con : ∀ {i}
          → IVec (X ∘ r i) js
          → X i

  record Alphabet
    {Γ Δ : Set}
    (X : Γ → Set)
    (V : Δ → Set)
    (K : Set)
    (r₀ : Δ → Γ)
    (r : Γ → Δ → Γ)
    : Set where
    field
      variable : ∀ {δ} → V δ → ∀ {γ} ⦃ _ : γ ≡ r₀ δ ⦄ → X γ
      constant : ∀ {γ} → K → X γ
      {#} : Nat
      functions : Vec (Recon X r) #

    data Term (γ : Γ) : Set
    data Function (γ : Γ) : ∀ {#} → Vec Δ # → Set

    data Term (γ : Γ) where
      υ : ∀ {δ} ⦃ _ : γ ≡ r₀ δ ⦄ → V δ → Term γ
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

I would like to precisify my idea that `Stronger` is, in some sense, better than or more generally useful than `Weaker`, and then prove it (in Agda).

Notice that if `Γ` is uninhabited, then so, obviously, is `Weaker.Alphabet`, but not `Stronger.Alphabet` (at least, not obviously).

```agda
¬Γ⇒¬Weaker :
  ∀ {Γ Δ : Set}
    (X : Γ → Set)
    (V : Δ → Set)
    (K : Set)
    (γ₀ : Γ)
    (r : Γ → Δ → Γ)
  → ¬ Γ
  → ¬ Weaker.Alphabet X V K γ₀ r
¬Γ⇒¬Weaker _ _ _ γ₀ _ ¬Γ _ = ¬Γ γ₀

¬[¬Γ⇒¬Stronger] :
  ¬ (∀ {Γ Δ : Set}
       (X : Γ → Set)
       (V : Δ → Set)
       (K : Set)
       (r₀ : Δ → Γ)
       (r : Γ → Δ → Γ)
     → ¬ Γ
     → ¬ Stronger.Alphabet X V K r₀ r)
¬[¬Γ⇒¬Stronger] ¬Γ⇒¬Stronger =
  ¬Γ⇒¬Stronger {⊥} {⊥} (λ _ → ⊤) (λ _ → ⊤) ⊤ id const id
    (record { variable = const tt ; constant = id ; # = 0 ; functions = [] })
```

Also notice that, as noted in the remark above, a `Stronger.Alphabet` can be constructed from any `Weaker.Alphabet`, in such a way that the parameters remain the same except that `r₀ ≔ r γ₀`.

```agda
module Weaker⇒Stronger
  {Γ Δ : Set}
  (X : Γ → Set)
  (V : Δ → Set)
  (K : Set)
  (γ₀ : Γ)
  (r : Γ → Δ → Γ)
  where

  IVec : ∀ {#} {js : Vec Δ #} {γ : Γ}
       → Stronger.IVec (X ∘ r γ) js
       → Weaker.IVec (X ∘ r γ) js
  IVec Stronger.[] = Weaker.[]
  IVec (x Stronger.∷ xs) = x Weaker.∷ IVec xs

  Con : ∀ {#} {js : Vec Δ #}
       → (∀ {γ} → Weaker.IVec (X ∘ r γ) js → X γ)
       → ∀ {γ} → Stronger.IVec (X ∘ r γ) js → X γ
  Con con xs = con (IVec xs)

  VecRecon : ∀ {#}
           → Vec (Weaker.Recon X r) #
           → Vec (Stronger.Recon X r) #
  VecRecon [] = []
  VecRecon ((js Weaker.▶ con) ∷ rcs) = (js Stronger.▶ Con con) ∷ VecRecon rcs

  Alphabet : Weaker.Alphabet X V K γ₀ r
           → Stronger.Alphabet X V K (r γ₀) r
  Alphabet record { variable = variable } .Stronger.Alphabet.variable = variable
  Alphabet record { constant = constant } .Stronger.Alphabet.constant = constant
  Alphabet record { # = # } .Stronger.Alphabet.# = #
  Alphabet record { functions = functions } .Stronger.Alphabet.functions = VecRecon functions
```

The above proofs capture much of what I mean by "more generally useful than", but not so the theorems. For example, a construction of `Stronger.Alphabet` could have been carried-out in a trivial manner:

```
module Trivially,Weaker⇒Stronger
  {Γ Δ : Set}
  (X : Γ → Set)
  (V : Δ → Set)
  (K : Set)
  (γ₀ : Γ)
  (r : Γ → Δ → Γ)
  where
  Alphabet : Weaker.Alphabet X V K γ₀ r
           → Stronger.Alphabet X V K (r γ₀) r
  Alphabet record { variable = variable } .Stronger.Alphabet.variable = variable
  Alphabet record { constant = constant } .Stronger.Alphabet.constant = constant
  Alphabet record { # = # } .Stronger.Alphabet.# = 0
  Alphabet record { functions = functions } .Stronger.Alphabet.functions = []
```

The construction of `Weaker⇒Stronger.Alphabet` is *equivalent* (in some sense) to its input, whereas its trivial counterpart is not. I have an idea (not a new one) of how to spell this out: there is a 1-1 map between the inhabitants of Weaker.Alphabet and a subset of the inhabitants of Stronger.Alphabet; I conjecture that `Weaker⇒Stronger.Alphabet` can be proven to be 1-1 while its trivial counterpart can be proven not to be.
