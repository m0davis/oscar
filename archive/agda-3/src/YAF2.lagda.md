
Yet more to do:

prove ∃gcd with an eye towards deciphering how to use the proof to construct a gcd

try interpreting a resolvable ambiguity: e.g. we don't know if '*' delimits code or comments, we try to parse a number in "blah * 12 * 50". In that case, we can conclude that " 12 " represents the number and "blah " and " 50" represent comments.

how about misspellings?!m

what can we infer about how to interpret something given a restatement and the fact that it is a fixed-point? how about vice-versa? how much something can we get out of nothing? consider "So you want to link your State data" and the EM algorithm.

Understand probable probabilities.

Compose Interpreters. See about tracking source code locations.


```agda
{-# OPTIONS --show-implicit #-}

module YAF2 where
```

Interpretation principles:

There are three types:
* Input : Set
* Output :



```agda
open import Prelude

∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃_ = Σ _

data IsYes {a} {P : Set a} : Dec P → Set a where
  yes : (p : P) → IsYes (yes p)

getProof : ∀ {a} {P : Set a} → {d : Dec P} → IsYes d → P
getProof (yes p) = p

record Function (domain : Set) (range : domain → Set) : Set₁ where
  field
    carrier : (x : domain) → range x → Set -- `translation`
    function-is-functional : (x : domain) (y1 y2 : range x) → carrier x y1 → carrier x y2 → y1 ≡ y2 -- no ambiguities
    function : (x : domain) → Dec $ Σ (range x) (carrier x) -- `interpret`

record SurjectiveFunction (domain : Set) (range : Set) : Set₁ where
  field
    f : Function domain (λ _ → range)
  open Function f
  field
    function-is-surjective : (y : range) → ∃ flip carrier y -- `restate`

module Peano (N : Set) (Z : N) (S : N → N) (_+_ _*_ : N → N → N) where

  record Axioms : Set₁ where
    field
      ax1 : ∀ x → ¬ (Z ≡ S x)
      ax2 : ∀ x y → S x ≡ S y → x ≡ y
      ind : (P : N → Set) → P Z → (∀ x → P x → P (S x)) → ∀ x → P x
      +-base : ∀ x → x + Z ≡ x
      +-ind : ∀ x y → x + S y ≡ S (x + y)

  _≟P_ : N → N → Bool
  x ≟P y = {!!}

  data _<P_ : N → N → Set where
    z<s : ∀ x → Z <P (S x)
    s<s : ∀ x y → S x <P S y

  _+P_ : N → N → N
  _+P_ x y = {!!}

∃→¬∀¬ : ∀ {a b} {A : Set a} {B : A → Set b} → Σ A B → ¬ (∀ x → ¬ B x)
∃→¬∀¬ (x , y) ∀¬ = ∀¬ x y

∀→¬∃¬ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ¬ Σ A (λ x → ¬ B x)
∀→¬∃¬ ∀′ (x , ¬y) = ¬y (∀′ x)

module ZermeloFrankel (E : Set) (S : Set) (_∈_ : E → S → Set) where

  record Axioms : Set₁ where
    field
      extensionality : ∀ x y → (∀ z → (z ∈ x → z ∈ y) × (z ∈ y → z ∈ x)) → x ≡ y
      -- regularity

record Interpreter (source target : Set) (translation : source → target → Set) (T : Function source (λ _ → target)) : Set where

  interpret' = Function.function T

  field
    interpret : (s : source) → Dec $ ∃ translation s -- possibly generate a translation into the target language (or show that no translation is possible)
    restate : (t : target) → ∃ flip translation t -- for any statement from the target language, there's a corresponding statement in the source

  field
    restate-sound : (t : target) (s : source) → s ≡ fst (restate t) → ∃ λ (r : translation s t) → interpret s ≡ yes (t , r) -- the interpretation of the restatement is the target -- this establishes that `interpret` inverts `restate`

    translation-is-canonical-1 : ∀ s t1 t2 → translation s t1 → translation s t2 → t1 ≡ t2 -- no ambiguities: multiple interpretations are not possible -- we could say that translation is "functional". Maybe this somehow calls for a separate record type.
    translation-is-canonical-2 : ∀ s t (r1 r2 : translation s t) → r1 ≡ r2 -- parsimony: there is but one way of translating a given source into a given target -- maybe this isn't something we want?

  paraphrase : (s : source) → IsYes (interpret s) → source
  paraphrase s i = fst ∘ restate ∘ fst $ getProof i

  -- paraphrase is a fixed-point if there is an interpretation
  field fixed-point : (s : source) → (i : IsYes (interpret s)) → ∃ λ i' → paraphrase (paraphrase s i) i' ≡ paraphrase s i
```

This is the dumbest parser I know: The way I expect the parser to go for a lagda file is to sort of dumbly look for certain control symbols that indicate the beginning and end of agda blocks, then feed the agda blocks to the next parser, having removed all the lagda commentary and control symbols.

This might be fine except what to do about situations where an agda comment block or agda string literal "contains" something that looks like a lagda control symbol. The solution is to require the control symbol to be on its own line, with no preceding spaces. It turns out that, though this makes some of what would have been valid agda code invalid, in all of those cases, there are other ways of writing the agda code equivalently.



We could have written the `Interpreter` so that it tries to decide if a unique transation exists. This would incorporate the no-ambiguities clause into `interpret`. Then, in `restate`, we would add that there is no other target which the generated source might be interpreted as. So, perhaps instead of `restate`, we call it `paraphrase`?

The point is to combine sources that have ambiguous translations in a way that (at least sometimes) we get an umambiguous whole. Another point is to be able to choose (at least sometimes) a "best" target out of all the possible ones. For example

a. 12
b. 12.
c. 12.3e
d. 12.3e16
e. twelve

1 :

Maybe a better example is:

a. ∀ { x : Nat } → P x ≡ "Hello, World\""
b. ∀{x:Nat}→Px≡"Hello, World\""

Let's assume that P, Px, _≡_, and Nat are definitely in scope. a. is easier to parse than b., in the sense that

Consider all the possible paraphrasings of

The character '∀' could be used in many ways:
* to hint the what follows is a list of pi-terms (rather than an application forming a single pi term)
* as part of an identifier
* as part of a string


has several possible

Here are the "senses" of each of the characters:
∀ = hint that the following is
{ =
