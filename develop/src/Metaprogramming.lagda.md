
# From datatypes to functions: Is it possible to derive programs without macros?

## Metaprogramming, inspired by Conor McBride's work on the same subject

```agda
module Metaprogramming where
```

### Some preliminaries that could be put elsewhere.

```agda
module Preliminary where

  open import Prelude public

  ∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃_ = Σ _

  data IsYes {a} {P : Set a} : Dec P → Set a where
    yes : (p : P) → IsYes (yes p)

  getProof : ∀ {a} {P : Set a} → {d : Dec P} → IsYes d → P
  getProof (yes p) = p

  add-zero : ∀ n → n ≡ n +N 0
  add-zero zero = refl
  add-zero (suc n) = cong suc (add-zero n)
```

### The hardcoded version that I would rather have derived

So, we've got ourselves a useless little language (I guess one that's enough for propositional logic):

```agda
module Hardcore where

  open Preliminary

  Universe = Nat

  data Alphabet (N : Nat) : Set where
    𝒰 : Universe → Alphabet N
    𝓋 : Fin N → Alphabet N
    ΠF : Alphabet N → Alphabet (suc N) → Alphabet N
    ΠI : Alphabet (suc N) → Alphabet N
    ΠE : Alphabet N → Alphabet N → Alphabet N
    𝟘F : Alphabet N
    𝟘E : Alphabet (suc N) → Alphabet N → Alphabet N
    𝟙F : Alphabet N
    𝟙I : Alphabet N
    𝟙E : Alphabet (suc N) → Alphabet N → Alphabet N → Alphabet N

  weakenFinFrom : ∀ {N} → Fin (suc N) → Fin N → Fin (suc N)
  weakenFinFrom zero x = suc x
  weakenFinFrom (suc from) zero = zero
  weakenFinFrom (suc from) (suc x) = suc (weakenFinFrom from x)

  weakenAlphabetFrom : ∀ {N} → Fin (suc N) → Alphabet N → Alphabet (suc N)
  weakenAlphabetFrom from (𝒰 ℓ) = 𝒰 ℓ
  weakenAlphabetFrom from (𝓋 x) = 𝓋 (weakenFinFrom from x)
  weakenAlphabetFrom from (ΠF a₀ a₁) = ΠF (weakenAlphabetFrom from a₀) (weakenAlphabetFrom (suc from) a₁)
  weakenAlphabetFrom from (ΠI a₀) = ΠI (weakenAlphabetFrom (suc from) a₀)
  weakenAlphabetFrom from (ΠE a₀ a₁) = ΠE (weakenAlphabetFrom from a₀) (weakenAlphabetFrom from a₁)
  weakenAlphabetFrom from 𝟘F = 𝟘F
  weakenAlphabetFrom from (𝟘E a₀ a₁) = 𝟘E (weakenAlphabetFrom (suc from) a₀) (weakenAlphabetFrom from a₁)
  weakenAlphabetFrom from 𝟙F = 𝟙F
  weakenAlphabetFrom from 𝟙I = 𝟙I
  weakenAlphabetFrom from (𝟙E a₀ a₁ a₂) = 𝟙E (weakenAlphabetFrom (suc from) a₀) (weakenAlphabetFrom from a₁) (weakenAlphabetFrom from a₂)
```

### A first attempt at a softer core

```agda
module Softcore-1 where
  open Preliminary
  open Hardcore using (Universe)
```

I would rather not have to write-out that big proof of weakenAlphabetFrom. But without a macro, I cannot automatically inspect the structure of Alphabet. And even if I did, isn't it a bit cumbersome to write-out the very structure of Alphabet? There's so much regularity there. Plus, a macro would not let us prove things about whole classes of similar datastructures in one go. Hence, metaprogramming.

There are three kinds of constructors to Alphabet: a constant, 𝒰, a variable, 𝓋, and the recursive constructors (all the rest). Although I guess 𝟘F is also a kind of constant, but in a vacuous way. So instead of "kinds of constructors", I characterise it in terms of kinds of arguments to constructors: the constant, Universe, the variable, Fin N, and the recursive kinds. Consider that the proof of weakenAlphabetFrom can be characterised by regular rules on each of those three classes. The meta-language on which we will rebuild Alphabet will rely on combinators of these three, so let's define it.

```agda
  data Grammar : Set₁ where
    constant : Set → Grammar
    variable : Grammar
    recursive : Nat → Grammar
```

Now, each constructor in Alphabet can be represented by a list of Grammar. And the data structure Alphabet itself can be represented by a list of *that*.

```agda
  alphabet : List (List Grammar)
  alphabet =
             (constant Universe ∷ [])
           ∷ (variable ∷ [])
           ∷ (recursive 0 ∷ recursive 1 ∷ [])
           ∷ (recursive 1 ∷ [])
           ∷ [] -- incomplete
```

We need a representation for when 𝔄lphabet is inhabited. At minimum, the representatation includes an indicator for which constructor is present. Let LA be the number of constructors of 𝔄lphabet. Then the representation includes Fin LA. For 𝒰, the representation would be (something like)

Fin LA × Universe

where the first of the pair is zero.

For the variable 𝓋 constructor, the representation would be

Fin LA × Fin N

where the first of the pair is (suc zero)

And for the recursive constructors, say ΠF, it's something like

Fin LA × (Fin LA × ...

Well, let's be more precise: for the inhabitant in a context of size 1 of ΠF (𝓋 0) (ΠI (𝓋 1)), we have

Fin LA × (Fin LA × Fin 1) × (Fin LA × (Fin LA × Fin 2))

having the value

2 , (1 , 0) , (3 , (1 , 1))

So we cannot construct the representation Fin LA × ... by the List (List Grammar) alone. We need more information: the value N : Nat, the first constructor inhabitant, Fin LA, and then ... so this is looking loopy again.

Notice that the inhabited value could have been specified as a list: 2 , 1 , 0 , 3 , 1 , 1, because constructor types tell us how many items are coming next. (This list is actually heterogeneous because of the possibility of constants, such as 𝒰.) The value of the first element, a Fin N, tells us the type of the next element. So, we have Fin N → Set, at least.

```agda
  LA : Nat
  LA = length alphabet

  nextElementType : (alphabet : List (List Grammar)) → (LA : Nat) → length alphabet ≡ LA → Fin LA → Set
  nextElementType [] .0 refl ()
  nextElementType ([] ∷ alphabet₂) LA@.(suc (length alphabet₂)) refl zero = Fin LA
  nextElementType ((constant x ∷ alphabet₁) ∷ alphabet₂) .(suc (length alphabet₂)) refl zero = x
  nextElementType ((variable ∷ alphabet₁) ∷ alphabet₂) .(suc (length alphabet₂)) refl zero = ∃ Fin
  nextElementType ((recursive x ∷ alphabet₁) ∷ alphabet₂) .(suc (length alphabet₂)) refl zero = Fin LA
  nextElementType (alphabet₁ ∷ alphabet₂) .(suc (length alphabet₂)) refl (suc p) = nextElementType alphabet₂ _ refl p
```

Okay, so... what?

Some possible things I could do:

module _ (alphabet : List (List Grammar) (LA : Nat) (isLength : length alphabet ≡ LA) where

  inferType : Fin LA → -- first of the inhabitant-list
              List (Σ Set λ A → A) → -- rest of inhabitants
              Maybe (∃ Set) -- a description of the constructed type, Fin LA × (Fin LA × ...  and an instance of its inhabitation


Having done this, we are now in a position to ask to build something like weaken𝔄lphabetFrom,

weaken𝔄lphabetFrom : ∀ {N} → Fin (suc N) → 𝔄lphabet N → 𝔄lphabet (suc N)

where we take the inhabitant-list and, under the assumption that inferType worked, we take the type and inhabitant and transform it to (surely) into a new type and term.

Can we tell if a given Set has the appropriate structure to be a representation of 𝔄lphabet?? We cannot case split on Set, so we can only do so if we can express this as a finite-length sentence. So, we cannot write represents𝔄lphabet : Set → Bool. However, if we constrain the size of the represented, 𝔄lphabet, then we can: represents𝔄lphabetWithDepth≤ : Nat → Set → Bool. Or can we? Can we write Set → Bool, where it's true iff the given Set is a Σ ?? Ah

```agda
  module TestSet where
    checksum : Set → Bool
    checksum x = {!!}

    checksum' : (S : Set) → Dec (Σ Set λ A → Σ (A → Set) λ B → S ≡ Σ A B)
    checksum' S = {!!}
```

Ah, no, of course not, because that would mean we could then case-split. But what I *can* do is make a Set that says that something is a Σ type (as I already did above, implicitly:

```agda
    isΣ : Set → Set₁
    isΣ S = Σ Set λ A → Σ (A → Set) λ B → S ≡ Σ A B
```

So, I'm trying to make something useful here with metaprogramming. I think that I can take a given (representation : List (Σ Set id)) and decide whether it represents some inhabitant of 𝔄lphabet, (alphabetical : Dec (isRepresentationOfSize≤ representation)). I could then take that representation and perform weakening on it. So a "something useful" is to define

  weaken : List (List Grammar) → List (Σ Set id) → Maybe (List (Σ Set id))

and for a fixed (alphabet : List (List Grammar)), which I have specifically designed to reflect 𝔄lphabet, I want to define

  show : ∃ 𝔄lphabet → List (Σ Set id)
  read : (s : List (Σ Set id)) → Dec (Σ (∃ 𝔄lphabet) λ r → show r ≡ s)

Is that possible? Consider a simpler one

  show' : MyData → Σ Set id
  read' : (s : Σ Set id) → Dec (Σ MyData λ r → show' r ≡ s)

But we cannot decide, of the Set, s₀, given to read', whether s₀ ≡ appropriate-set-for-MyData.

Hmm....


Let's see about what we could do with a macro.


```agda
  module MacroExplore where
    open import Tactic.Reflection
    open Hardcore

    toptype : evalT (getType (quote Alphabet)) ≡
      pi (vArg (def₀ (quote Nat))) (Abs.abs "N" (agda-sort (lit 0)))
    toptype = refl

    topstructure : evalT (getDefinition (quote Alphabet)) ≡
      data-type 1
      (quote 𝒰 ∷
       quote 𝓋 ∷
       quote ΠF ∷
       quote ΠI ∷
       quote ΠE ∷
       quote 𝟘F ∷ quote 𝟘E ∷ quote 𝟙F ∷ quote 𝟙I ∷ [ quote 𝟙E ])
    topstructure = refl

    subtype : evalT (getType (quote 𝒰)) ≡
      pi (hArg (def₀ (quote Nat)))
        (Abs.abs "N"
         (pi (vArg (def₀ (quote Universe)))
          (Abs.abs "_" (def₁ (quote Alphabet) (var₀ 1)))))
    subtype = refl

    substructure : evalT (getDefinition (quote 𝒰)) ≡
      data-cons (quote Alphabet)
    substructure = refl


    subtype' : evalT (getType (quote ΠF)) ≡
      pi (hArg (def₀ (quote Nat)))
        (Abs.abs "N"
         (pi (vArg (def₁ (quote Alphabet) (var₀ 0)))
          (Abs.abs "_"
           (pi (vArg (def₁ (quote Alphabet) (con₁ (quote Nat.suc) (var₀ 1))))
            (Abs.abs "_" (def₁ (quote Alphabet) (var₀ 2)))))))
    subtype' = refl

    substructure' : evalT (getDefinition (quote ΠF)) ≡
      data-cons (quote Alphabet)
    substructure' = refl
```

So, there is a macro that could take my Alphabet and generate weakenAlphabetFrom.

So, I have been wanting to "do things" with the Alphabet data structure. But when I metaprogram, there's no "data" anymore. Maybe what I need is an induction principal so that I can define functions on the ersatz Alphabet data structure.

Consider a datatype

data 𝔄 (N : Nat) where
  v : Fin N → 𝔄 N

What's the induction principal??

ind𝔄 : ∀ N → (C : 𝔄 N → Set) →
       → (∀ (v0 : Fin N) → C (v v0))
       (an : 𝔄 N) → C N an

okay, pretty uninteresting b/c it's not recursive. How about...

data 𝔄2 (N : Nat) where
    𝓋 : Fin N → Alphabet N
    ΠF : Alphabet N → Alphabet (suc N) → Alphabet N

ind𝔄2 : (C : ∀ N → 𝔄2 N → Set) →
        → (indV : ∀ N → (v0 : Fin N) → C N (v v0))
        → (indΠF : ∀ N → (ΠF' : 𝔄2 N) (ΠF'' : 𝔄2 (suc N)) →
                       C N ΠF' → C (suc N) ΠF'' → C N (ΠF ΠF' ΠF''))
        → ∀ N → (an : 𝔄2 N) → C N an

{- thought about cubes in high demnitnos
postulate
  ℕ : Set

(n : ℕ) → (p p' : Point n) → p ≢ p' → Edge n p p' × Point (suc n)
-}

So the idea hit me (or vice versa) that what was lacking in the `alphabet` try above was a `data` structure to help keep an anchor for recursive calls.

### A second attempt at a softer core

```agda
module Softcore-2 where
  open Preliminary
  open Hardcore using (Universe)
  open Softcore-1 using (Grammar; constant; variable; recursive)
```

```agda
  data Alphabet (N : Nat) : List Grammar → Set where
    𝒰 : Alphabet N (constant Universe ∷ [])
    𝓋 : Alphabet N (variable ∷ [])
    ΠF : Alphabet N (recursive 0 ∷ recursive 1 ∷ [])
    ΠI : Alphabet N (recursive 1 ∷ [])
{- incomplete: this is here as a reminder about the original `Alphabet`
    ΠE : Alphabet N → Alphabet N → Alphabet N
    𝟘F : Alphabet N
    𝟘E : Alphabet (suc N) → Alphabet N → Alphabet N
    𝟙F : Alphabet N
    𝟙I : Alphabet N
    𝟙E : Alphabet (suc N) → Alphabet N → Alphabet N → Alphabet N
-}
```

Well, I can see that this is not going to work either: I have no way to recurse through the Alphabet structure without a macro.

To continue development, I may need to review McBride's work, Dependently Type Metaprogramming (in Agda).
