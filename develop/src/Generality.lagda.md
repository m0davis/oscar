
# Generality: being as general as possible, but not any more so (h/t Einstein)

```agda
module Generality where
```

```agda
open import Prelude
open import Tactic.Nat
```

## replacing a type with a family of types

In a development of [Alphabet](Alphabet.lagda.md), I defined the following system and remarked:

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
    constructor _//_//_
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
    constructor _//_//_
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

```agda
module Weaker⇒Stronger-1-1
  {Γ Δ : Set}
  (X : Γ → Set)
  (V : Δ → Set)
  (K : Set)
  (γ₀ : Γ)
  (r : Γ → Δ → Γ)
  where
  open Weaker⇒Stronger X V K γ₀ r
  W = Weaker.Alphabet X V K γ₀ r

  1-1 : ∀ (w w' : W) → Alphabet w ≡ Alphabet w' → w ≡ w'
  1-1 (variable Weaker.// constant // functions) (variable' Weaker.// constant' // functions') s≡s' rewrite cong Stronger.Alphabet.variable s≡s' | cong Stronger.Alphabet.constant s≡s' = {!!}
  {- Goal: _≡_ {lzero} {Weaker.Alphabet {Γ} {Δ} X V K γ₀ r}
           (Weaker._//_//_ variable' constant' {.#} functions)
           (Weaker._//_//_ variable' constant' {.#₁} functions')
     ————————————————————————————————————————————————————————————
     ...
     functions'
               : Vec {lzero} (Weaker.Recon {Γ} {Δ} X r) .#₁
     .#₁       : Nat
     functions : Vec {lzero} (Weaker.Recon {Γ} {Δ} X r) .#
     .#        : Nat
     ...
  -}
  {- The trick of `rewrite`ing using `cong` does not work quite so easily when dependent variables are involved (in this case, the type of `functions` depends on `.#`. -}
```

## collapsing parameter types

In the same development later on, I continued to worry about ad-hoc-ness of the parameterisation:

> Is there any gain to be had from having separate types `Γ` and `Δ`? Considering that both `variable` and `Term.υ` demand that `γ ≡ r₀ δ`, and that `r₀` is not used in any other way, I have my suspicions.

I now explore whether this claim can be given further justification. To start, I define a new system where `Γ` and `Δ` are collapsed.

```agda
module Collapsed where

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
    {Γ : Set}
    (X : Γ → Set)
    (V : Γ → Set)
    (K : Set)
    (r : Γ → Γ → Γ)
    : Set where
    constructor _//_//_
    field
      variable : ∀ {γ} → V γ → X γ
      constant : ∀ {γ} → K → X γ
      {#} : Nat
      functions : Vec (Recon X r) #

    data Term (γ : Γ) : Set
    data Function (γ : Γ) : ∀ {#} → Vec Γ # → Set

    data Term (γ : Γ) where
      υ : V γ → Term γ
      κ : K → Term γ
      φ : (f : Fin #)
        → Function γ (Recon.js (indexVec functions f))
        → Term γ

    data Function (γ : Γ) where
      [] : Function γ []
      _∷_ : ∀ {δ} → Term (r γ δ)
          → ∀ {#δs} {δs : Vec Γ #δs} → Function γ δs
          → Function γ (δ ∷ δs)

    reifyTerm : ∀ {γ} → Term γ → X γ
    reifyFunction : ∀ {γ} {#δs} {δs : Vec Γ #δs}
               → Function γ δs
               → IVec (X ∘ r γ) δs

    reifyTerm (υ v) = variable v
    reifyTerm (κ k) = constant k
    reifyTerm (φ f Φ) = Recon.con (indexVec functions f) (reifyFunction Φ)
    reifyFunction {δs = []} _ = []
    reifyFunction {δs = δ ∷ δs} (τ ∷ Φ) = reifyTerm τ ∷ reifyFunction Φ
```

Next, a mapping from `Stronger.Alphabet` to `Collapsed.Alphabet`. The trouble is, it can't be done in a way that isn't obviously not 1-1. In `Stronger`, `X` and `V` are families indexed on two different types, whereas they are the same in `Collapsed`. We can account for this via the projection `r₀ : Δ → Γ` such that inhabitants of `Collapsed`'s `Γ` are no more than the inhabitants of `Stronger`'s `Δ`. However, when it comes to defining `r` in `Collapsed`, we need a way of projecting from two inhabitants of `Stronger`'s `Δ` back into `Stronger`'s `Δ`, but nothing from `Stronger` can help with that. The obvious candidate, `r`, projects into `Γ`. You can see my predicament here:

```agda
module Stronger⇒Collapsed
  {Γ Δ : Set}
  (X : Γ → Set)
  (V : Δ → Set)
  (K : Set)
  (r₀ : Δ → Γ)
  (r : Γ → Δ → Γ)
  where
  postulate
    Alphabet : Stronger.Alphabet X V K r₀ r
             → Collapsed.Alphabet (X ∘ r₀) V K (λ γ δ → {!!})
```

On the other hand, is there a 1-1 mapping from `Collapsed` to a subset of `Stronger`? This unfinished proof of a mapping (not necessarily 1-1) suggests to me that there is one.

```agda
module Collapsed⇒Stronger
  {Γ : Set}
  (X : Γ → Set)
  (V : Γ → Set)
  (K : Set)
  (r : Γ → Γ → Γ)
  where
  Alphabet : Collapsed.Alphabet X V K r
           → Stronger.Alphabet X V K id r
  Alphabet (Collapsed._//_//_ variable constant {#} functions) .Stronger.Alphabet.variable v ⦃ refl ⦄ = variable v
  Alphabet (Collapsed._//_//_ variable constant {#} functions) .Stronger.Alphabet.constant = constant
  Alphabet (Collapsed._//_//_ variable constant {#} functions) .Stronger.Alphabet.# = #
  Alphabet (Collapsed._//_//_ variable constant {zero} []) .Stronger.Alphabet.functions = []
  Alphabet (Collapsed._//_//_ variable constant {suc #} (function ∷ functions)) .Stronger.Alphabet.functions = {!function!} ∷ {!!}
```

## Reflections (or Diversions?)

Given the above, I reverse my previous suspicion that there was nothing to be gained from having separate types `Γ` and `Δ`. The obvious question is, what have we gained?

I would like to find a language that `Stronger` can describe but `Collapsed` cannot. In the failed attempt to map `Stronger` to `Collapsed`, I could have gone further had if there had been an available mapping `collapse : Γ → Δ`. Certainly if `Δ = ⊥` and `Γ` is any inhabited type, there would be no such mapping.

### a diversion

Suppose we have it then that, for some constant R,

    Δ = ⊥
    Γ = Nat
    X = λ γ → Fin γ
    V = λ _ → Nat
    r₀ = λ _ → R
    r = λ γ _ → suc γ

What sort of `Alphabet` could this be? Recall our model of `variable` constructors:

    variable : ∀ {δ} → V δ → ∀ {γ} ⦃ _ : γ ≡ r₀ δ ⦄ → X γ

Following the equations, the type that `variable` projects to is Fin R. So, there are R variables. If `R = zero`, there are no variables! So, to say very little, we have gained, with the separation of types `Γ` and `Δ`, the ability to describe languages that have few variables.

To say a little more, I imagine a modeling a finite state machine, such as a digital computer with a certain fixed number of binary registers. Such a language might be useful in describing its states and functions.

* Illustrate the the language imagined for modeling a finite state machine and prove that `Collapsed` cannot describe it.

I can see that the above is mistaken because if `Δ = ⊥`, then we cannot have `r₀ = λ _ → R` but only `r₀ = λ ()`.

### to continue, going nowhere?

...and by implication, there would be no variables either, since `V : Δ → Set`. But `Collapsed` could model this aspect by setting `V ≔ λ _ → ⊥`. With `Δ = ⊥`, the `Recon.js` field of a `Recon X r` is `Vec ⊥ #`, so such a `record` would need `Recon.# = zero`, so then `Recon.js = []`, and the type of `Recon.con` becomes `∀ {i} → IVec (X ∘ r i) [] → X i`, where the first visible argument is trivially inhabited by `IVec.[]`, so the type of `Alphabet.functions` becomes equivalent to `Vec X #` (importantly, this is `Alphabet.#`, which is not necessarily `zero`). I am describing the following class of `Alphabet`s.

```agda
module Δ=⊥
  {Γ : Set}
  (X : Γ → Set)
  (K : Set)
  (constant : ∀ {γ} → K → X γ)
  (# : Nat)
  (functions : Vec (Stronger.Recon {Γ} {⊥} X λ _ ()) #)
  where
  stronger : Stronger.Alphabet {Δ = ⊥} X (λ ()) K (λ ()) (λ _ ())
  stronger .Stronger.Alphabet.variable {()} x
  stronger .Stronger.Alphabet.constant k = constant k
  stronger .Stronger.Alphabet.# = #
  stronger .Stronger.Alphabet.functions = functions
```

Here is a particular member of that class:

```agda
module Member = Δ=⊥ (Fin ∘ suc) Nat (λ { {γ} x → zero }) 2 (([] Stronger.▶ λ x → zero) ∷ ([] Stronger.▶ λ x → zero) ∷ [])
```

But it is now that I realise that I do not have a clear idea of what it means to "find a language that `Stronger` can describe but `Collapsed` cannot".

# Further research

* Say more precisely what it means "to find a language that `Stronger` can describe but `Collapsed` cannot". It may be helpful to consider what was discovered from `¬Γ⇒¬Weaker` and `¬[¬Γ⇒¬Stronger]`.

* Assuming that we indeed have, discover *why* we have gained by separating types `Γ` and `Δ`. Can we gain still further? Following an intuition I have, could it help to making one dependent on the other? Or to index each on a common type?

* Complete and clean-up the proof `Collapsed⇒Stronger.Alphabet`.

* Formalise a definition of a "1-1 mapping" with an eye towards defining what it means to be "more generally useful than".

* What then to say about the relation between "ad-hoc", "more generally useful than", and "1-1"? I seem to confirm fears about ad-hoc-ness of a given system by proving there is another system for which there is a 1-1 map "into it" from the alleged ad-hoc system. But how to put such fears to rest? Is there a certain respect in which I can say that a system is "most generally useful"?
