
What was once a single topic has become several. The contents of this file will be parceled out to others, or otherwise junked.

```agda
module BurnAfterReading where
```

-------------------------------------------------------------------------



# From datatypes to functions: Is it possible to derive programs without macros?

## Metaprogramming, inspired by Conor McBride's work on the same subject

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

I would rather not have to write-out that big proof of weakenAlphabetFrom. By using a macro (a form of metaprogramming), I could inspect `Alphabet`'s structure, infer the constructor for variables, and build a suitable `weakenAlphabetFrom`.

That solution is unappealing to me. Macros construct functions as kind-of one-shot deals: I would not be able to say something general about datatypes "similar" (in some sense) to `Alphabet`. For example, suppose I want to say that all datatypes of the (not-yet-specified) "kind" which `Alphabet` is an instance are such that there is a "weakening" function with such-and-such properties. The existence of the macro I guess is a kind of meta-level proof thereof, but it's not a proof *in Agda*, and I can't use a meta-level proof to build programs.

Hence the qualifier, "(in Agda)", in Conor McBride's, "Dependently Typed Metaprogramming (in Agda)".

### A first attempt at a softer core

```agda
module Softcore-1 where
  open Preliminary
  open Hardcore using (Universe)
```

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

To continue development, I may need to review McBride's work, Dependently Typed Metaprogramming (in Agda).

### A proof-of-concept that Indexed Containers can represent the `Alphabet`

```agda
module IndexedContainers-ProofOfConcept where
  open import Prelude
```

The indexed container:

```agda
  record _▷_ (I J : Set) : Set₁ where
    constructor _◁_$_
    field
      ShIx : J → Set
      PoIx : (j : J) → ShIx j → Set
      riIx : (j : J) (s : ShIx j) → PoIx j s → I
    ⟦_⟧ᵢ : (I → Set) → J → Set
    ⟦_⟧ᵢ X j = Σ (ShIx j) λ s → (p : PoIx j s) → X (riIx j s p)
  open _▷_ public using (⟦_⟧ᵢ)
```

`Alphabet` as one of those containers

```agda
  data Letter : Set where
    𝒰 𝓋 ΠF ΠI : Letter

  Letter×FV = Letter × Nat -- the second represents the number of free variables

  alphabetContainer : Letter×FV ▷ Letter×FV
  alphabetContainer ._▷_.ShIx (𝒰 , _) = Nat
  alphabetContainer ._▷_.ShIx (𝓋 , N) = Fin N
  alphabetContainer ._▷_.ShIx (ΠF , _) = Vec Letter 2
  alphabetContainer ._▷_.ShIx (ΠI , _) = Vec Letter 1
  alphabetContainer ._▷_.PoIx (𝒰 , _) _ = Fin 0
  alphabetContainer ._▷_.PoIx (𝓋 , _) _ = Fin 0
  alphabetContainer ._▷_.PoIx (ΠF , _) _ = Fin 2
  alphabetContainer ._▷_.PoIx (ΠI , _) _ = Fin 1
  alphabetContainer ._▷_.riIx (𝒰 , N) s ()
  alphabetContainer ._▷_.riIx (𝓋 , N) s ()
  alphabetContainer ._▷_.riIx (ΠF , N) (x ∷ _) zero = x , N
  alphabetContainer ._▷_.riIx (ΠF , N) (_ ∷ x ∷ _) (suc zero) = x , suc N
  alphabetContainer ._▷_.riIx (ΠF , N) s (suc (suc ()))
  alphabetContainer ._▷_.riIx (ΠI , N) (x ∷ s) zero = x , suc N
  alphabetContainer ._▷_.riIx (ΠI , N) s (suc ())
```

##### Petersson-Synek Trees

```agda
  data ITree {J : Set} (C : J ▷ J) (j : J) : Set where
    ⟨_⟩ : ⟦ C ⟧ᵢ (ITree C) j → ITree C j

  demo : ITree alphabetContainer (ΠF , 3)
  demo = ⟨ 𝒰 ∷ ΠI ∷ [] , (λ { zero → ⟨ 4 , (λ { ()}) ⟩ ; (suc zero) → ⟨ 𝓋 ∷ [] , (λ { zero → ⟨ 3 , (λ { ()}) ⟩ ; (suc ())}) ⟩ ; (suc (suc ()))}) ⟩
```

So, at least I can see, by `demo` that I have some sort of metaprogrammatic grasp on the `Alphabet` datatype. But can I do more?

### The (not-really-working) Metaprogrammatic "softcore" (non-)Solution to the `Hardcore.Alphabet` problem

```agda
module Softcore-3 where
  open Preliminary
  open Hardcore using (Universe; weakenFinFrom)
```

After a slightly-less cursory (but still cursory) review, I developed the following, not-so-working program.

I assume I can define a suitable version of weakening a Fin by a certain amount:

```agda
  postulate
    weakenFinFromBy : ∀ {N} → Fin (suc N) → Fin N → (by : Nat) → Fin (N + by)
```

I define indexed containers and Petersson-Synek Trees, a la McBride's 4th chapter.

```agda
  record _▷_ {α} (I J : Set α) : Set (lsuc α) where
    constructor _◁_$_
    field
      ShIx : J → Set α
      PoIx : (j : J) → ShIx j → Set α
      riIx : (j : J) (s : ShIx j) → PoIx j s → I
    ⟦_⟧ᵢ : (I → Set α) → J → Set α
    ⟦_⟧ᵢ X j = Σ (ShIx j) λ s → (p : PoIx j s) → X (riIx j s p)
  open _▷_ public using (⟦_⟧ᵢ)

  data ITree {α} {J : Set α} (C : J ▷ J) (j : J) : Set α where
    ⟨_⟩ : ⟦ C ⟧ᵢ (ITree C) j → ITree C j
```

```agda
  data Grammar : Set where
    universe : Grammar
    variable : Grammar
    recursive : ∀ {N} → Vec Nat N → Grammar

  data Symbol : Grammar → Set where
    𝒰 : Symbol universe
    𝓋 : Symbol variable
    ΠF : Symbol (recursive (0 ∷ 1 ∷ []))
    ΠI : Symbol (recursive (1 ∷ []))
    ΠE : Symbol (recursive (0 ∷ 0 ∷ []))
    𝟘F : Symbol (recursive [])
    𝟘E : Symbol (recursive (1 ∷ 0 ∷ []))
    𝟙F : Symbol (recursive [])
    𝟙I : Symbol (recursive [])
    𝟙E : Symbol (recursive (1 ∷ 0 ∷ 0 ∷ []))
```

```agda
  FV = Nat -- the number of free variables
  Clause = Σ Grammar Symbol × FV -- not sure what to call this

  shape : Clause → Set
  shape ((universe , _) , _) = Universe
  shape ((variable , _) , N) = Fin N
  shape ((recursive {N} _ , _) , _) = Vec (Σ Grammar Symbol) N

  wkShape : {ga : Σ Grammar Symbol} {fv : FV} → shape (ga , fv) → shape (ga , suc fv)
  wkShape {universe , snd₁} x = x
  wkShape {variable , snd₁} x = suc x
  wkShape {recursive x₁ , snd₁} x = x

  posit : (j : Clause) → Set
  posit ((universe , _) , _) = ⊥
  posit ((variable , _) , _) = ⊥
  posit ((recursive {N} _ , _) , _) = Fin N

  recurse : (j : Clause) → (s : shape j) → posit j → Clause
  recurse ((universe , _) , _) _ ()
  recurse ((variable , _) , _) _ ()
  recurse ((recursive binders , _) , N) recursors v = indexVec recursors v , N + indexVec binders v

  alphabetContainer : Clause ▷ Clause
  alphabetContainer = shape ◁ (λ j _ → posit j) $ recurse

  demo1 : ITree alphabetContainer ((_  , ΠI) , 3)
  demo1 = ⟨ (variable , 𝓋) ∷ [] , (λ { (zero) → ⟨ {!!} , (λ { (())}) ⟩ ; ((suc ()))}) ⟩
  -- the hole has the correct number of free variables

  demo2 : ITree alphabetContainer ((universe , 𝒰) , 0)
  demo2 = ⟨ 3 , (λ ()) ⟩

  demo3 : ITree alphabetContainer ((_ , ΠF) , 0)
  demo3 = ⟨ (_ , 𝒰) ∷ (_ , 𝒰) ∷ [] , (λ { zero → ⟨ 3 , (λ ()) ⟩ ; (suc zero) → ⟨ 2 , (λ ()) ⟩ ; (suc (suc ()))}) ⟩

  WeakenAlphabetFrom : ∀ (ea : Σ Grammar Symbol) → ∀ {N} → Fin (suc N) → ITree alphabetContainer (ea , N) → ITree alphabetContainer (ea , suc N)

  {-# TERMINATING #-}
  WeakenAlphabetFromR : ∀ {V} (binders : Vec Nat V)
                              (gas : Vec (Σ Grammar Symbol) V)
                          {N : Nat} (from : Fin (suc N))
    → (recursor : (p : Fin V)
                → ITree alphabetContainer (indexVec gas p , N + indexVec binders p))
    → (p : Fin V)
    → ITree alphabetContainer (indexVec gas p , suc (N + indexVec binders p))

  WeakenAlphabetFrom (universe , _) _ ⟨ ℓ , _ ⟩ = ⟨ ℓ , (λ ()) ⟩
  WeakenAlphabetFrom (variable , _) from ⟨ v , _ ⟩ = ⟨ weakenFinFrom from v , (λ ()) ⟩
  WeakenAlphabetFrom (recursive binders , _) from ⟨ gas , recursor ⟩ = ⟨ gas , WeakenAlphabetFromR binders gas from recursor ⟩

  WeakenAlphabetFromR [] gas from recursor ()
  WeakenAlphabetFromR (binder ∷ binders) ((g , a) ∷ gas) {N} from recursor p with indexVec ((g , a) ∷ gas) p | indexVec (binder ∷ binders) p | recursor p
  WeakenAlphabetFromR (binder ∷ binders) ((g , a) ∷ gas) {N} from recursor p | universe , a' | ib | ⟨ sh , po ⟩ = {!!}
  WeakenAlphabetFromR (binder ∷ binders) ((g , a) ∷ gas) {N} from recursor p | variable , a' | ib | ⟨ sh , po ⟩ = {!!}
  WeakenAlphabetFromR (binder ∷ binders) ((g , a) ∷ gas) {N} from recursor p | recursive bs , a' | ib | ⟨ sh , po ⟩ = ⟨ sh , (λ p₁ → WeakenAlphabetFromR bs sh (weakenFinFromBy zero from ib) po p₁) ⟩
```

I have not convinced Agda that the weakening function terminates. I guess that I need something which is equivalent to an induction principle for the `ITree`, and that this is the same sort of thing called for in exercise 4.10. McBride mentions there: "This is not an easy exercise."

So, I definitely need to seriously study that work. After that, hopefully a solution will be presented in a section below.

...

After realising that sometimes it is easier to prove a stronger theorem than a weaker one, I thought of trying again. First, I'll review where I get stuck in `WeakenAlphabetFrom`.

```agda
  WAF' : ∀ (ea : Σ Grammar Symbol) → ∀ {N} → Fin (suc N) → ITree alphabetContainer (ea , N) → ITree alphabetContainer (ea , suc N)
  WAF' (universe , _) _ ⟨ ℓ , _ ⟩ = ⟨ ℓ , (λ ()) ⟩
  WAF' (variable , _) from ⟨ v , _ ⟩ = ⟨ weakenFinFrom from v , (λ ()) ⟩
  WAF' (recursive bs , _) from ⟨ gys , r ⟩ = ⟨ gys , (λ p → WAF' (indexVec gys p) (weakenFinFromBy zero from (indexVec bs p)) (r p)) ⟩
```

...and magically, with no explanation whatsoever, the solution falls into my lap. I guess I just got better at doing proofs by induction.

I ought to be able to prove a version of the above that works not just for alphabetContainer (which is based on a particular symbol-set, `Symbol`, but for any symbol-set indexed by `Grammar` (i.e. for any (Symbol : Grammar → Set).

### A serious study of Dependently Typed Metaprogramming (in Agda)

#### Chapter 1

```agda
module DependentlyTypedMetaprogramming-Chapter1 where
```

(this section not yet written)

#### Chapter 2

```agda
module DependentlyTypedMetaprogramming-Chapter2 where
  open Preliminary
```

2.1 Syntax

```agda
  data ⋆ : Set where
    ι : ⋆
    _▶_ : ⋆ → ⋆ → ⋆
  infixr 5 _▶_

  data Cx (X : Set) : Set where
    ε : Cx X
    _,,_ : Cx X → X → Cx X
  infixl 4 _,,_

  data _∈_ (τ : ⋆) : Cx ⋆ → Set where
    zero : ∀ {Γ} → τ ∈ Γ ,, τ
    suc : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ ,, σ
  infix 3 _∈_

  -- well-typed terms
  data _⊢_ (Γ : Cx ⋆) : ⋆ → Set where
    var : ∀ {τ}
          → τ ∈ Γ
          → Γ ⊢ τ
    lam : ∀ {σ τ}
          → Γ ,, σ ⊢ τ
          → Γ ⊢ σ ▶ τ
    app : ∀ {σ τ}
          → Γ ⊢ σ ▶ τ → Γ ⊢ σ
          → Γ ⊢ τ
  infix 3 _⊢_
```

##### A naive approach to weakening

```agda
  module NaiveWeakening where
```

I wonder if I can "weaken" a well-typed term.

```agda
    module WeakenTry1 where
      weaken⊢ : ∀ {Γ τ δ} → Γ ⊢ τ → Γ ,, δ ⊢ τ
      weaken⊢ (var τ∈Γ) = var (suc τ∈Γ)
      weaken⊢ {ε} {δ = δ} (lam {_} (var zero)) = lam (var zero)
      weaken⊢ {ε} {δ = δ} (lam {σ} (var (suc ())))
      weaken⊢ {ε} {δ = δ} (lam {σ} (lam {ρ} Γ,σ⊢τ)) = {!!} -- I am stuck here
      weaken⊢ {ε} {δ = δ} (lam {σ} (app Γ,σ⊢τ Γ,σ⊢τ₁)) = {!!}
      weaken⊢ {Γ ,, x} {δ = δ} (lam {σ} Γ,σ⊢τ) = {!!}
      weaken⊢ (app Γ⊢σ▶τ Γ⊢σ) = {!!}
```

*That* strategy doesn't give me much hope. Maybe a different one?

```agda
    module WeakenTry2 where
      weaken⊢ : ∀ {Γ τ δ} → Γ ⊢ τ → Γ ,, δ ⊢ τ
      weaken⊢ (var τ∈Γ) = var (suc τ∈Γ)
      weaken⊢ {ε} {δ = ι} (lam {ι} {ι} (var zero)) = lam (var zero)
      weaken⊢ {ε} {δ = ι} (lam {ι} {ι} (var (suc x))) = lam (var zero)
      weaken⊢ {ε} {δ = ι} (lam {ι} {ι} (app {σ} x x₁)) = lam (var zero)
      weaken⊢ {ε} {δ = δ ▶ δ₁} (lam {ι} {ι} x) = lam (var zero)
      weaken⊢ {ε} {δ = ι} (lam {σ ▶ σ₁} {ι} x) = lam (var (suc zero))
      weaken⊢ {ε} {δ = δ ▶ δ₁} (lam {σ ▶ σ₁} {ι} (var (suc ())))
      weaken⊢ {ε} {δ = δ ▶ δ₁} (lam {σ ▶ σ₁} {ι} (app {ι} σ▶σ₁⊢ι▶ι σ▶σ₁⊢ι)) = {!!} -- I am stuck here
      weaken⊢ {ε} {δ = δ ▶ δ₁} (lam {σ ▶ σ₁} {ι} (app {σ₂ ▶ σ₃} x x₁)) = {!!}
      weaken⊢ {ε} {δ = δ} (lam {σ} {τ ▶ τ₁} x) = {!!}
      weaken⊢ {Γ ,, x₁} (lam x) = {!!}
      weaken⊢ (app x x₁) = {!!}
```

Let me now check that what I'm thinking is even possible. Consider a term that is constructed via `lam`.

```agda
    module CheckThinking where
      lam-conned = (ι ▶ ι) ▶ ((ι ▶ ι) ▶ ι) ▶ ι

      proof-in-ε : ε ⊢ lam-conned
      proof-in-ε = lam (lam (app (var zero) (var (suc zero))))
```

Now check that I can add any term to the context and get a proof of the same term

```agda
      proof-in-ε,δ : ∀ δ → ε ,, δ ⊢ lam-conned
      proof-in-ε,δ δ = lam (lam (app (var zero) (var (suc zero))))
```

Returning now to `weaken⊢`, I conjecture that, at least in the case where we start with a null context, and try to throw in another arbitrary supposition, the structure of the new proof should be the same as the given one. I shall now try to prove it just in the case of a null context.

```agda
    module WeakenTry3-null-context where
      weakenε⊢ : ∀ {τ δ} → ε ⊢ τ → ε ,, δ ⊢ τ
      weakenε⊢ (var x) = var (suc x)
      weakenε⊢ (lam (var zero)) = lam (var zero)
      weakenε⊢ (lam (var (suc x))) = lam (var (suc (suc x))) -- nope, the structures differ!
      weakenε⊢ (lam (lam x)) = lam (lam {!!}) -- I get stuck here
      weakenε⊢ (lam (app x x₁)) = lam {!!}
      weakenε⊢ (app x x₁) = {!!}
```

In the place where I get stuck, I want to have proved a stronger theorem. In this case, a theorem (S1) that says that if I've proved Γ ⊢ τ, then I can also prove δ ++ Γ ⊢ τ. Perhaps then the real solution is to say (S2) what I *really* mean: given any Γ ⊢ τ, and any G generated by taking, in any order, every element of Γ and any number of other terms, I can also prove G ⊢ τ.

I'll try S1 as a start. First, I will need to define what it means to prepend to a context.

```agda
    module WeakenTry4-stronger-theorem-S1 where
      infixr 21 _∙_
      _∙_ : ⋆ → Cx ⋆ → Cx ⋆
      δ ∙ ε = ε ,, δ
      δ ∙ (Γ ,, γ) = (δ ∙ Γ) ,, γ
```

And the (successful) proof (which should be reorganised to extract the lemma?):

```agda
      weaken∙⊢ : ∀ {Γ τ δ} → Γ ⊢ τ → δ ∙ Γ ⊢ τ
      weaken∙⊢ {ε} (var τ∈δ) = var (suc τ∈δ)
      weaken∙⊢ {Γ ,, x₁} (var zero) = var zero
      weaken∙⊢ {Γ ,, x₁} (var (suc τ∈Γ)) = var (suc (lemma τ∈Γ)) where
        lemma : ∀ {Γ δ τ} → τ ∈ Γ → τ ∈ (δ ∙ Γ)
        lemma {ε} ()
        lemma {Γ ,, γ} zero = zero
        lemma {Γ ,, γ} (suc τ∈Γ) = suc (lemma τ∈Γ)
      weaken∙⊢ (lam Γ,σ⊢τ) = lam (weaken∙⊢ Γ,σ⊢τ)
      weaken∙⊢ (app Γ⊢σ▶τ Γ⊢σ) = app (weaken∙⊢ Γ⊢σ▶τ) (weaken∙⊢ Γ⊢σ)
```

Next perhaps is to show that I can swap any two consecutive elements of a context. But for that, I will need a more robust version of append.

```agda
      _+++_ : Cx ⋆ → Cx ⋆ → Cx ⋆
      ε +++ Δ = Δ
      (Γ ,, δ) +++ Δ = Γ +++ (δ ∙ Δ)
```

The following is very more messy than need be.

```agda
      +++=∙ : ∀ {δ Γ} → (δ ∙ Γ) ≡ (ε ,, δ) +++ Γ
      +++=∙ {Γ = Γ} = refl

      stable-left-∈∙ : ∀ {τ Γ δ} → τ ∈ Γ → τ ∈ δ ∙ Γ
      stable-left-∈∙ {Γ = ε} ()
      stable-left-∈∙ {Γ = Γ ,, γ} zero = zero
      stable-left-∈∙ {Γ = Γ ,, γ} (suc τ∈Γ) = suc (stable-left-∈∙ τ∈Γ)

      allow : ∀ {Γ Δ γ} → γ ∈ Γ +++ (Δ ,, γ)
      allow {ε} {Δ} = zero
      allow {Γ ,, x} {Δ} = allow {Γ} {x ∙ Δ}

      very-okay : ∀ {τ Γ Δ ρ} → τ ∈ Γ +++ Δ → τ ∈ Γ +++ (Δ ,, ρ)
      very-okay {Γ = ε} {ε} ()
      very-okay {Γ = Γ ,, x₁} {ε} x = very-okay {Γ = Γ} x
      very-okay {Γ = ε} {Δ ,, x₁} zero = suc zero
      very-okay {Γ = ε} {Δ ,, x₁} (suc x) = suc (suc x)
      very-okay {Γ = Γ ,, x₂} {Δ ,, x₁} x = very-okay {_} {Γ} {x₂ ∙ Δ ,, x₁} x

      split∙ : ∀ {τ γ Δ} → τ ∈ γ ∙ Δ → Either (τ ∈ ε ,, γ) (τ ∈ Δ)
      split∙ {Δ = ε} = left
      split∙ {Δ = Δ ,, δ} zero = right zero
      split∙ {γ = γ} {Δ = Δ ,, δ} (suc τ∈γΔ) with split∙ {Δ = Δ} τ∈γΔ
      split∙ {γ = γ} {Δ ,, δ} (suc τ∈γΔ) | left zero = left zero
      split∙ {γ = γ} {Δ ,, δ} (suc τ∈γΔ) | left (suc ())
      split∙ {γ = γ} {Δ ,, δ} (suc τ∈γΔ) | right τ∈Δ = right (suc τ∈Δ)

      split : ∀ {Γ Δ τ} → τ ∈ Γ +++ Δ → Either (τ ∈ Γ) (τ ∈ Δ)
      split {ε} τ∈Δ = right τ∈Δ
      split {Γ ,, γ} {ε} τ∈Γγ with split {Γ = Γ} τ∈Γγ
      split {Γ ,, γ} {ε} τ∈Γγ | left τ∈Γ = left (suc τ∈Γ)
      split {Γ ,, γ} {ε} τ∈Γγ | right zero = left zero
      split {Γ ,, γ} {ε} τ∈Γγ | right (suc ())
      split {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ with split {Γ = Γ} τ∈ΓγΔδ
      split {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | left τ∈Γ = left (suc τ∈Γ)
      split {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | right zero = right zero
      split {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | right (suc τ∈γΔ) with split∙ {Δ = Δ} τ∈γΔ where
      split {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | right (suc τ∈γΔ) | left zero = left zero
      split {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | right (suc τ∈γΔ) | left (suc ())
      split {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | right (suc τ∈γΔ) | right τ∈Δ = right (suc τ∈Δ)

      stable-left-∈+++ : ∀ {τ Γ Δ} → τ ∈ Δ → τ ∈ Γ +++ Δ
      stable-left-∈+++ {Γ = ε} {Δ} τ∈Δ = τ∈Δ
      stable-left-∈+++ {Γ = Γ ,, x} {Δ} τ∈Δ = stable-left-∈+++ {Γ = Γ} (stable-left-∈∙ τ∈Δ)

      prepend-stable : ∀ {Δ} δ → δ ∈ δ ∙ Δ
      prepend-stable {ε} δ = zero
      prepend-stable {Δ ,, x} δ = suc (prepend-stable {Δ} δ)

      stable-right-∈+++' : ∀ {τ Γ Δ} → τ ∈ Γ → τ ∈ Γ +++ Δ
      stable-right-∈+++' {τ} {ε ,, .τ} {ε} zero = zero
      stable-right-∈+++' {τ} {Γ ,, x ,, .τ} {ε} zero = stable-left-∈+++ {Γ = Γ} {Δ = ε ,, x ,, τ} zero
      stable-right-∈+++' {Γ = .(_ ,, _)} {ε} (suc τ∈Γ) = stable-right-∈+++' {Δ = ε ,, _} τ∈Γ
      stable-right-∈+++' {Γ = ε} {Δ ,, x} ()
      stable-right-∈+++' {Γ = Γ ,, x₁} {Δ ,, x} zero = stable-left-∈+++ {x₁} {Γ = Γ} {Δ = x₁ ∙ Δ ,, x} (suc (prepend-stable {Δ} x₁))
      stable-right-∈+++' {τ} {Γ = Γ ,, x₁} {Δ ,, x} (suc τ∈Γ) = stable-right-∈+++' {τ} {Γ} {x₁ ∙ Δ ,, x} τ∈Γ

      superduper-okay : ∀ {τ Γ Δ γ ρ} → τ ∈ Γ +++ (γ ∙ Δ) → τ ∈ Γ +++ (ρ ∙ γ ∙ Δ)
      superduper-okay {τ} {Γ} {Δ} {γ} {ρ} x with split {Γ} {γ ∙ Δ} x
      superduper-okay {τ} {Γ} {Δ} {γ} {ρ} x | left x₁ = stable-right-∈+++' {Δ = (ρ ∙ γ ∙ Δ)} x₁
      superduper-okay {τ} {Γ} {Δ} {γ} {ρ} x | right x₁ = stable-left-∈+++ {Γ = Γ} (stable-left-∈∙ {τ} {γ ∙ Δ} x₁)

      still-good : ∀ {τ Γ Δ ρ} → τ ∈ Γ +++ Δ → τ ∈ Γ +++ (ρ ∙ Δ)
      still-good {Γ = ε} {ε} ()
      still-good {Γ = ε} {Δ ,, δ} zero = zero
      still-good {Γ = ε} {Δ ,, δ} (suc τ∈Δ) = suc (still-good {Γ = ε} τ∈Δ)
      still-good {Γ = Γ ,, γ} {ε} τ∈Γγ = very-okay {Γ = Γ} τ∈Γγ
      still-good {Γ = Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ with split {Γ = Γ} τ∈ΓγΔδ
      still-good {_} {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | left x = stable-right-∈+++' {Δ = (γ ∙ _ ∙ Δ ,, δ)} x
      still-good {_} {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | right zero = allow {Γ = Γ} {Δ = γ ∙ _ ∙ Δ} {δ}
      still-good {τ} {Γ ,, γ} {Δ ,, δ} τ∈ΓγΔδ | right (suc x) = stable-left-∈+++ {Γ = Γ} (suc (still-good {τ} {ε ,, γ} {Δ} {_} x ))

      insert∈ : ∀ {Γ γ Δ} → γ ∈ (Γ +++ (γ ∙ Δ))
      insert∈ {ε} {γ} {ε} = zero
      insert∈ {ε} {γ} {Δ ,, x} = suc (insert∈ {ε} {γ} {Δ})
      insert∈ {Γ ,, γ'} {γ} {ε} = allow {Γ} {ε ,, γ'} -- insert∈ {Γ} {γ} {{!!}}
      insert∈ {Γ ,, γ'} {γ} {Δ ,, δ'} =
        let γ∈ΓγΔδ' = insert∈ {Γ} {γ} {Δ ,, δ'}
        in
        very-okay {Γ = Γ} (stable-left-∈+++ {Γ = Γ} {Δ = γ' ∙ γ ∙ Δ} (stable-left-∈∙ {Γ = γ ∙ Δ} (prepend-stable {Δ = Δ} γ)))

      stable-right-∈+++ : ∀ {τ Γ Δ} → τ ∈ Γ → τ ∈ Γ +++ Δ
      stable-right-∈+++ {Γ = ε} ()
      stable-right-∈+++ {Γ = Γ ,, γ} {ε} zero = insert∈ {Γ} {γ} {ε}
      stable-right-∈+++ {Γ = Γ ,, γ} {Δ ,, x} zero = insert∈ {Γ} {γ} {Δ ,, x}
      stable-right-∈+++ {Γ = Γ ,, γ} {Δ} (suc τ∈Γ) = stable-right-∈+++ {_} {Γ} τ∈Γ

      appendRight∈ : ∀ {Γ Δ τ} → τ ∈ Γ → τ ∈ Γ +++ Δ
      appendRight∈ {ε} {ε} ()
      appendRight∈ {Γ ,, γ} {ε} zero = insert∈ {Γ} {_} {ε}
      appendRight∈ {Γ ,, γ} {ε} (suc τ∈Γ) = appendRight∈ τ∈Γ
      appendRight∈ {ε} {Δ ,, δ} ()
      appendRight∈ {Γ ,, γ} {Δ ,, δ} zero = insert∈ {Γ = Γ} {γ} {Δ ,, δ}
      appendRight∈ {Γ ,, γ} {Δ ,, δ} (suc τ∈Γ) = appendRight∈ τ∈Γ

      swaplemma : ∀ {Γ Δ δ₁ δ₂ τ} → τ ∈ (Γ ,, δ₁ ,, δ₂) +++ Δ → τ ∈ (Γ ,, δ₂ ,, δ₁) +++ Δ
      swaplemma {ε} {ε} zero = suc zero
      swaplemma {ε} {ε} (suc zero) = zero
      swaplemma {ε} {ε} (suc (suc ()))
      swaplemma {ε} {_ ,, _} zero = zero
      swaplemma {ε} {Δ ,, _} (suc τ∈δ₁δ₂Δ) = suc (subswaplemma {Δ = Δ} τ∈δ₁δ₂Δ) where
        subswaplemma : ∀ {δ₁ δ₂ Δ τ} → τ ∈ δ₁ ∙ δ₂ ∙ Δ → τ ∈ δ₂ ∙ δ₁ ∙ Δ
        subswaplemma {Δ = ε} zero = suc zero
        subswaplemma {Δ = ε} (suc zero) = zero
        subswaplemma {Δ = ε} (suc (suc ()))
        subswaplemma {Δ = Δ ,, δ} zero = zero
        subswaplemma {δ₁} {δ₂} {Δ = Δ ,, δ} (suc τ∈δ₁δ₂Δ) = suc (subswaplemma {Δ = Δ} τ∈δ₁δ₂Δ)
      swaplemma {Γ ,, γ} {ε} {δ₁} {δ₂} τ∈Γεγδ₁δ₂ with split {Γ = Γ} τ∈Γεγδ₁δ₂ module L where
      swaplemma {Γ ,, γ} {ε} {δ₁} {δ₂} τ∈Γεγδ₁δ₂ | left τ∈Γ = appendRight∈ τ∈Γ where
      swaplemma {Γ ,, γ} {ε} {δ₁} {δ₂} τ∈Γεγδ₁δ₂ | right zero = stable-left-∈+++ {Γ = Γ} (suc zero)
      swaplemma {Γ ,, γ} {ε} {δ₁} {δ₂} τ∈Γεγδ₁δ₂ | right (suc zero) = stable-left-∈+++ {Γ = Γ} zero
      swaplemma {Γ ,, γ} {ε} {δ₁} {δ₂} τ∈Γεγδ₁δ₂ | right (suc (suc zero)) = stable-left-∈+++ {Γ = Γ} (suc (suc zero))
      swaplemma {Γ ,, γ} {ε} {δ₁} {δ₂} τ∈Γεγδ₁δ₂ | right (suc (suc (suc ())))
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ with split {Γ = Γ} x₁
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | left x = stable-right-∈+++ {Δ = γ ∙ δ₂ ∙ δ₁ ∙ Δ ,, δ} x
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right zero = stable-left-∈+++ {Γ = Γ} zero
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) with split∙ {Δ = δ₁ ∙ δ₂ ∙ Δ} x
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | left zero = stable-left-∈+++ {Γ = Γ} (suc (prepend-stable {Δ = δ₂ ∙ δ₁ ∙ Δ} γ))
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | left (suc ())
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | right x₂ with split∙ {Δ = δ₂ ∙ Δ} x₂
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | right x₂ | left zero = stable-left-∈+++ {Γ = Γ} (suc (stable-left-∈∙ {Γ = δ₂ ∙ δ₁ ∙ Δ} (stable-left-∈∙ {Γ = δ₁ ∙ Δ} (prepend-stable {Δ = Δ} δ₁))))
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | right x₂ | left (suc ())
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | right x₂ | right x₃ with split∙ {Δ = Δ} x₃
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | right x₂ | right x₃ | left zero = {!!}
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | right x₂ | right x₃ | left (suc ())
      swaplemma {Γ ,, γ} {Δ ,, δ} {δ₁} {δ₂} x₁ | right (suc x) | right x₂ | right x₃ | right x₄ = {!!} -- stable-left-∈+++ {Γ = Γ} (suc ({!split∙ x!}))

      swapΓ⊢ : ∀ {Γ Δ δ₁ δ₂ τ} → (Γ ,, δ₁ ,, δ₂) +++ Δ ⊢ τ → (Γ ,, δ₂ ,, δ₁) +++ Δ ⊢ τ
      swapΓ⊢ {Γ} {Δ} {δ₁} {δ₂} {τ} (var x) = var (swaplemma {Γ = Γ} {Δ = Δ} {δ₁ = δ₁} {δ₂ = δ₂} x)
      swapΓ⊢ {Γ} {ε} {δ₁} {δ₂} {.(σ ▶ _)} (lam {σ} Γδ₁δ₂Δσ⊢τ) = lam {!swapΓ⊢ {Γ} {ε} {δ₁} {δ₂} !}
      swapΓ⊢ {ε} {Δ ,, x} {δ₁} {δ₂} {.(σ ▶ _)} (lam {σ} Γδ₁δ₂Δσ⊢τ) = lam {!!}
      swapΓ⊢ {Γ ,, x₁} {Δ ,, x} {δ₁} {δ₂} {.(σ ▶ _)} (lam {σ} Γδ₁δ₂Δσ⊢τ) = lam {!!} -- lam {!!}
      swapΓ⊢ {Γ} {Δ} {δ₁} {δ₂} {τ} (app x x₁) = app (swapΓ⊢ {Γ} {Δ} {δ₁} {δ₂} x) (swapΓ⊢ {Γ} {Δ} {δ₁} {δ₂} x₁)
```

swapΓ⊢ seems not powerful enough to recursively prove itself in the case of `lam`. I am still getting stuck trying to prove that a certain reordering of prependings to Δ makes no difference *when followed by conses*.

So, maybe my thought of a much stronger theorem (S2) was the right idea. I could delay that for now and instead try to prove that simple reorderings of Γ make no difference. But...

I think at this point I need to figure out why the last approach did not work.

To review, I successfully proved (s0) that Γ⊢τ → γ,Γ⊢τ. This turned out to only require a lemma having to do with context membership (∈), I guess because all of the rules for well-typed terms (⊢) at most manipulate the head of the context. I then tried to prove (s*) Γ,γ₁,γ₂,Δ⊢τ → Γ,γ₂,γ₁,Δ⊢τ. However, this turned out to require a proof of (s**) Γ,γ₁,γ₂,Δ,σ⊢τ → Γ,γ₂,γ₁,Δ,σ⊢τ. That surprised me because I thought that (s**) was just an instance of (s*) with Δ ≔ Δ,σ. Apparently, that is not exactly correct.

To see why (or why not), I compare this to a situation with lists: Γ,γ₂,γ₁,Δ,σ is the equivalent of σ ∷ (Δ ++ (γ₁ ∷ γ₂ ∷ Γ)). In (s*), I am trying to show that for a given X : Set, and any P : List X → Set, that
  if P (Δ ++ (γ₁ ∷ γ₂ ∷ Γ)) then P (Δ ++ (γ₂ ∷ γ₁ ∷ Γ)).
Previously (in s0), I proved that
  if P Δ then P (Δ ++ [ γ ]).
With these together, could we prove that P (γ ∷ Δ) when P Δ? In the case that Δ = [], we just use (s0) with Δ = []. In the case that Δ = δ ∷ Δ', we have by hypothesis P (δ ∷ Δ') and it suffices to prove P (γ ∷ δ ∷ Δ'). By (s*), it suffices to prove P (δ ∷ γ ∷ Δ'). ...and now a bit of a gag... In the case that Δ' = [], we have by hypothesis P (δ ∷ []) and it sufficies to prove P (δ ∷ γ ∷ []), which follows from (s0). But in the case that Δ' = δ' ∷ Δ'', we have P (δ ∷ δ' ∷ Δ'') and it suffices to prove P (δ ∷ γ ∷ δ' ∷ Δ''), but by (s*) it suffices to prove P (δ ∷ δ' ∷ γ ∷ Δ''). ...and so on.

I am guessing that such a proof by induction works much better (read: at all) by tracking the length of the list in the induction hypothesis. So, instead of proving things for any (P : List X → Set), we try for any (N : Nat) and (P : Vec X N → Set).

Let me see if that holds up. First, let's see that such a thing is hard with Lists:

```agda
    module HardWithLists where
      open Preliminary
      postulate
        X : Set
        P : List X → Set
        s0 : ∀ Δ γ → P Δ → P (Δ ++ [ γ ])
        s* : ∀ Δ γ₁ γ₂ Γ → P (Δ ++ (γ₁ ∷ γ₂ ∷ Γ)) → P (Δ ++ (γ₂ ∷ γ₁ ∷ Γ))
      car-P : ∀ γ Γ → P Γ → P (γ ∷ Γ)
      car-P γ [] = s0 [] γ
      car-P γ [ γ₁ ] Pγ₁Γ = s* [] _ _ [] (s0 [ γ₁ ] γ Pγ₁Γ)
      car-P γ (γ₁ ∷ γ₂ ∷ Γ) Pγ₁γ₂Γ = {!!}
```

Yut, it's pretty hard. But maybe if I had taken `with length Γ` or something, it might have worked out. But let's do the equivalent with vectors and see if it's easier.

```agda
    module EasierWithVectors where
      open Preliminary
      v[_] : ∀ {X : Set} → X → Vec X 1
      v[ x ] = pure x
      postulate
        X : Set
        P : ∀ {N} → Vec X N → Set
        s0 : ∀ {N} (Δ : Vec X N) γ → P Δ → P (Δ v++ v[ γ ])
        s* : ∀ {N M} (Δ : Vec X N) γ₂ γ₁ (Γ : Vec X M) → P (Δ v++ (γ₁ ∷ γ₂ ∷ Γ)) → P (Δ v++ (γ₂ ∷ γ₁ ∷ Γ))
      car-P : ∀ {M} γ (Γ : Vec X M) → P Γ → P (γ ∷ Γ)
      car-P γ [] PΓ = s0 [] γ PΓ
      car-P γ (γ₁ ∷ []) Pγ₁Γ = s* [] γ γ₁ [] (s0 v[ γ₁ ] γ Pγ₁Γ)
      car-P {.2} γ (γ₁ ∷ _∷_ {.0} γ₂ []) Pγ₁γ₂Γ = s* [] γ γ₁ v[ γ₂ ] (s* v[ γ₁ ] γ γ₂ [] (s0 (γ₁ ∷ γ₂ ∷ []) γ Pγ₁γ₂Γ))
      car-P {.(suc (suc (suc _)))} γ (γ₁ ∷ _∷_ {.(suc _)} γ₂ (γ₃ ∷ Γ)) Pγ₁γ₂γ₃Γ = s* [] γ γ₁ (γ₂ ∷ γ₃ ∷ Γ) (s* v[ γ₁ ] γ γ₂ (γ₃ ∷ Γ) (s* (γ₁ ∷ γ₂ ∷ []) γ γ₃ Γ {!!}))
```

No, that's looking just as hard. Perhaps the problem was needing a stronger induction hypothesis.

```agda
    module StrongerInductionHypothesis where
      open Preliminary
      open HardWithLists
      stronger-P : ∀ Δ γ Γ → P (Δ ++ Γ) → P (Δ ++ γ ∷ Γ)
      stronger-P [] γ [] x = s0 [] γ x
      stronger-P (d ∷ Δ) γ [] x = transport P {!!} (s0 (d ∷ Δ ++ []) γ x)
      stronger-P Δ γ (x₁ ∷ Γ) x = s* Δ x₁ γ Γ (transport P {!!} (stronger-P (Δ ++ [ x₁ ]) γ Γ (transport P {!!} x)))
```

The above would maybe work if only Agda knew a few equivalences, such as d ∷ (Δ ++ []) ++ [ γ ] ≡ d ∷ Δ ++ [ γ ]. That should be relatively easy, as it is orthogonal to `P`. Did we even need the stronger induction hypothesis? (I think we did.)

##### McBride's approach to weakening

Boy oh boy was the above tough. I am astonished that McBride has found a solution in just a few lines.

```agda
  -- Ren Γ Δ = Γ ⊆ Δ ; subsetting of contexts
  Ren : Cx ⋆ → Cx ⋆ → Set
  Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ

  -- wkr = Γ ⊆ Δ → Γ,σ ⊆ Δ,σ ; subsetting invariance under one-at-a-time prefixing
  wkr : ∀ {Γ Δ σ} → Ren Γ Δ → Ren (Γ ,, σ) (Δ ,, σ)
  wkr r zero = zero
  wkr r (suc i) = suc (r i)

  -- Γ <>< Ξ = Γ,Ξ
  _<><_ : Cx ⋆ → List ⋆ → Cx ⋆
  xz <>< [] = xz
  xz <>< (x ∷ xs) = xz ,, x <>< xs
  infixl 4 _<><_

  -- weak = Γ ⊆ Γ,Ξ ; subsetting identity?
  weak : ∀ {Γ} Ξ → Ren Γ (Γ <>< Ξ)
  weak [] i = i
  weak (_ ∷ Ξ) i = weak Ξ (suc i)

  -- Sub Γ Δ = Δ ≼ Γ ; subproperty relation ; Δ makes as least as many claims as Γ ; theories of Γ are at least as strong (or stronger) as Δ.
  -- Δ ⊢ Γ
  Sub : Cx ⋆ → Cx ⋆ → Set
  Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Δ ⊢ τ

  -- Shub Γ Δ = ∀ Ξ . Δ,Ξ ≼ Γ,Ξ ; Δ ⋆≼⋆ Γ
  -- Δ ⊢Ξ Γ
  Shub : Cx ⋆ → Cx ⋆ → Set
  Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

  -- ren = Γ ⊆ Δ → Δ ⋆≼⋆ Γ
  -- Γ ⊆ Δ → Δ ⊢Ξ Γ
  ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
  ren r [] = var ∘ r
  ren r (_ ∷ Ξ) = ren (wkr r) Ξ

  -- θ //   -- Δ ⋆≼⋆ Γ → Δ ≼ Γ
  -- Δ ⊢Ξ Γ → Δ ≼ Γ
  _//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Γ ⊢ τ → Δ ⊢ τ
  θ // var i = θ [] i
  θ // lam t = lam ((θ ∘ _∷_ _) // t)
  θ // app f s = app (θ // f) (θ // s)
```

So, we obtain:

```agda
  module McBrideWeakening where
    weaken⊢ : ∀ {Γ τ δ} → Γ ⊢ τ → Γ ,, δ ⊢ τ
    weaken⊢ {Γ} {τ} {δ} Γ⊢τ = ren (weak (δ ∷ [])) // Γ⊢τ
```

The furthest I will go with reverse-engineering this is to say:

```agda
    weaken⊢₁ : ∀ {Γ τ δ} → Γ ⊢ τ → Γ ,, δ ⊢ τ
    weaken⊢₁ = ren suc //_
```

Here is the general form of McBride's weakening theorem:

```agda
    weaken⊢⋆ : ∀ {Γ τ Ξ} → Γ ⊢ τ → Γ <>< Ξ ⊢ τ
    weaken⊢⋆ {Ξ = Ξ} = ren (weak Ξ) //_
```

I wonder if the ease with which McBride solved this problem comes down to the difference in our functions for expanding contexts. That is, my adder `_+++_` vs his fish `_<><_`. Here is a go at proving the above `swaplemma` with the friendly fish.

```agda
  module FishesForSnakes where
    swaplemma : ∀ {Γ δ₁ δ₂ τ} Δ → τ ∈ (Γ ,, δ₁ ,, δ₂) <>< Δ → τ ∈ (Γ ,, δ₂ ,, δ₁) <>< Δ
    swaplemma [] zero = suc zero
    swaplemma [] (suc zero) = zero
    swaplemma [] (suc (suc i)) = suc (suc i)
    swaplemma {Γ} {δ₁} {δ₂} {τ} (δ ∷ Δ) i = {!!} -- I get stuck here
```

At the point where I get stuck, my instinct is to write a function that decides membership in a list,

  _∈L?_ : ∀ τ Δ → Dec (τ ∈ ε <>< Δ)

and then another that shows that membership is stable under suffixing:

  stable : ∀ τ Γ Δ → τ ∈ ε <>< Δ → τ ∈ Γ <>< Δ

...and as I keep thinking about this I realise there are more and more functions I will need. Maybe the trouble is that I am approaching the problem as a matter of how to make a deduction or make an argument that something is so, rather than... well, something else ... I have the intuition that it would be something "more constructive", in a way. This reminds me of what it's like to learn to use mathematical induction, except in some way this is harder for the very fact that I can see an alternative solution (or anyway, I have a mirage of a simple solution, which turns out to be a monster).

Trying another idea... Suppose I had tried a stronger version of the weakening theorem. To start, here's the weak one:

```agda
  module FishesForSnakes-2 where
    weaken-weak : ∀ {Γ δ τ} → Γ ⊢ τ → Γ ,, δ ⊢ τ
    weaken-weak (var i) = var (suc i)
    weaken-weak (lam Γ,σ⊢τ) = lam {!!} -- I get stuck here
    weaken-weak (app x x₁) = {!!}
```

The goal is Γ,δ,σ⊢τ and I'm given Γ,σ⊢τ. I'm unable to use weaken-weak to prove this, but if I had a stronger theorem capable of proving that Γ,δ,σ⊢τ given Γ,σ⊢τ, then it might work out.

```agda
    ∈-lemma : ∀ {Γ Δ Ξ τ} → τ ∈ Γ <>< Δ → τ ∈ Γ <>< Ξ <>< Δ
    ∈-lemma = {!!}

    weaken-stronger : ∀ {Γ Δ Ξ τ} → Γ <>< Δ ⊢ τ → Γ <>< Ξ <>< Δ ⊢ τ
    weaken-stronger {Γ} {Δ} {[]} ΓΔ⊢τ = ΓΔ⊢τ
    weaken-stronger {ε} {[]} {ξ ∷ Ξ} (var ())
    weaken-stronger {ε} {[]} {ξ ∷ Ξ} (lam {σ = σ} ΓΔ⊢τ) = lam (weaken-stronger {ε ,, ξ} {σ ∷ []} {Ξ} (weaken-stronger {ε} {σ ∷ []} {ξ ∷ []} ΓΔ⊢τ))
    weaken-stronger {ε} {[]} {ξ ∷ Ξ} {τ} (app {σ} ΓΔ⊢σ▶τ ΓΔ⊢σ) = app {Γ = ε ,, ξ <>< Ξ} {σ = σ} (weaken-stronger {ε} {[]} {ξ ∷ Ξ} {σ ▶ τ} ΓΔ⊢σ▶τ) (weaken-stronger {ε} {[]} {ξ ∷ Ξ} {σ} ΓΔ⊢σ)
    weaken-stronger {Γ ,, γ} {[]} {ξ ∷ Ξ} (var x) = var (∈-lemma {Γ ,, γ} {[]} {ξ ∷ Ξ} x) where
    weaken-stronger {Γ ,, γ} {[]} {ξ ∷ Ξ} (lam ΓΔ⊢τ) = lam (weaken-stronger {Γ ,, γ} {_ ∷ []} {ξ ∷ Ξ} ΓΔ⊢τ)
    weaken-stronger {Γ ,, γ} {[]} {ξ ∷ Ξ} (app ΓΔ⊢τ ΓΔ⊢τ₁) = {!!}
    weaken-stronger {Γ} {δ ∷ Δ} {ξ ∷ Ξ} (var x) = var (∈-lemma {Γ} {δ ∷ Δ} {ξ ∷ Ξ} x)
    weaken-stronger {ε} {δ ∷ Δ} {ξ ∷ Ξ} (lam {σ} ΓΔ⊢τ) = lam {!!}
    weaken-stronger {Γ ,, γ} {δ ∷ Δ} {ξ ∷ Ξ} (lam {σ} ΓΔ⊢τ) = lam {!weaken-stronger {Γ ,, γ} {ε ,, δ} {ξ ∷ Ξ}!} -- I get stuck here
    -- ((ε ,, δ) <>< Δ) ,, σ
    weaken-stronger {Γ} {δ ∷ Δ} {ξ ∷ Ξ} (app ΓΔ⊢τ ΓΔ⊢τ₁) = {!!}
```

Where I get stuck, I would need to append a σ to the end of Δ, which is what the `lam` adds to the context, but I can't without adding another level of recursion, because Δ is a list. How about adding yet another condition to the theorem, making it even stronger?

```agda
    even-stronger : ∀ Γ Δ Ξ Ψ τ → Γ <>< Δ ⊢ τ → Γ <>< Ξ <>< Δ <>< Ψ ⊢ τ
    even-stronger Γ Δ Ξ Ψ τ (var x) = {!!}
    even-stronger Γ Δ Ξ [] .(_ ▶ _) (lam x) = lam {!!}
    even-stronger Γ Δ Ξ (ψ ∷ Ψ) .(_ ▶ _) (lam {σ} x) = lam {!!} -- stuck here
    even-stronger Γ Δ Ξ Ψ τ (app x x₁) = {!!}
```

Nope, the problem again is that the thing I want to add to the part in the Δ position is to be added to the end of the list.

In my search for how I could have come up with McBride's solution on my own, I now return to the idea of (S2). Roughly speaking, I want to state that, given Γ ⊢ τ, and any Δ such that Γ ⊆ Δ, Δ ⊢ τ. For the weakening theorem, in particular, I would want to prove that Γ ⊆ Γ ,, δ. When I first had the notion of S2, I did not consider that I could state "⊆" with something like McBride's "Ren". A couple of paths to take:

(P1) What did I have in mind to say "⊆"? And would that have worked?

(P2) How would I state (S2) in McBride's terms?

Starting with latter, the stronger statement S2 would be:

```agda
  module StrongerAlaMcBride where
    S2 : ∀ Γ Δ → (∀ τ → τ ∈ Γ → τ ∈ Δ) → ∀ {τ} → Γ ⊢ τ → Δ ⊢ τ
    S2 Γ Δ Γ⊆Δ (var τ∈Γ) = var (Γ⊆Δ _ τ∈Γ)
    S2 Γ Δ Γ⊆Δ {.(σ ▶ τ)} (lam {σ} {τ} Γσ⊢τ) =
      let Δσ⊢τ : Δ ,, σ ⊢ τ
          Δσ⊢τ = S2 (Γ ,, σ) (Δ ,, σ) (λ t t∈Γσ → case t∈Γσ of λ { zero → zero ; (suc t∈Γ) → suc (Γ⊆Δ _ t∈Γ)}) Γσ⊢τ
      in lam Δσ⊢τ
    S2 Γ Δ Γ⊆Δ {.τ} (app {σ} {τ} Γ⊢σ▶τ Γ⊢σ) =
      let Δ⊢σ▶τ : Δ ⊢ σ ▶ τ
          Δ⊢σ▶τ = S2 Γ Δ Γ⊆Δ Γ⊢σ▶τ
          Δ⊢σ : Δ ⊢ σ
          Δ⊢σ = S2 Γ Δ Γ⊆Δ Γ⊢σ
      in app Δ⊢σ▶τ Δ⊢σ
```

Well that was easy. A solution in three (long) lines. Maybe the `case_of_` counts as an extra two lines, so five lines. That leads me to think of another path to take:

(P2a) How would I refine the `StrongerAlaMcBride` solution to be more elegant? How close does this come to McBride's solution?

Continuing directly,

```agda
    infix 3 _⊆_
    _⊆_ : Cx ⋆ → Cx ⋆ → Set
    Γ ⊆ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ

    wk⊆ : ∀ {Γ Δ} → Γ ⊆ Δ → ∀ {σ} → Γ ,, σ ⊆ Δ ,, σ
    wk⊆ Γ⊆Δ zero = zero
    wk⊆ Γ⊆Δ (suc τ∈Γ) = suc (Γ⊆Δ τ∈Γ)

    infix 3 _≽_
    _≽_ : Cx ⋆ → Cx ⋆ → Set
    Γ ≽ Δ = ∀ {τ} → Γ ⊢ τ → Δ ⊢ τ

    wk⊢ : ∀ {Γ Δ} → Γ ⊆ Δ → Γ ≽ Δ
    wk⊢ Γ⊆Δ (var τ∈Γ) = var (Γ⊆Δ τ∈Γ)
    wk⊢ Γ⊆Δ (lam Γσ⊢τ) = lam (wk⊢ (wk⊆ Γ⊆Δ) Γσ⊢τ)
    wk⊢ Γ⊆Δ (app Γ⊢σ▶τ Γ⊢σ) = app (wk⊢ Γ⊆Δ Γ⊢σ▶τ) (wk⊢ Γ⊆Δ Γ⊢σ)

    wk⊢₁ : ∀ {Γ δ} → Γ ≽ Γ ,, δ
    wk⊢₁ = wk⊢ suc
```

* It's interesting that `_∈_.suc` can be read as a kind of weakening: Γ ⊆ Γ ,, δ.

In the above refinement, the subsetting notion `_⊆_` amounts to McBride's notion of renaming `Ren`, whereas the subproperty notion `_≽_` doesn't correspond to particular named notion in his work. Perhaps I will discover why certain other ideas (e.g. substitution) were introduced later on.

Returning to (P1), my idea had been to consider all arrangements of supersets of a context. I would have built a data structure describing this notion in the following manner.

Assume M and N are natural numbers, M ≤ N. Assume Ξ is any ordered sequence of M - N elements. Let the length of Γ be M and the length of Δ (as desired) be N. Consider all functions f : Fin M → Fin N such that f x = f y only if x = y. Construct a quasi-inverse f⁻¹ : Fin N → Maybe (Fin M) such that . Let Δ₀ be empty. Let Ξ₀ = Ξ. We can construct Δ in N steps. At step n, if f (n - 1) = nothing, let Δₙ = Δₙ₋₁ ,, ξ, where ξ is the first element of Ξₙ₋₁, and let Ξₙ be the remainder. But if f (n - 1) = just γ, then let Δₙ = Δₙ₋₁ ,, γ and let Ξₙ = Ξₙ₋₁. Finally, declare Δ = Δ_N.

I will now try to translate that somehow into real constructive mathematics.

[snip]

Actually, no, trying to do that directly gets hairy.

Another approach I might consider would be to consider all surjective functions from Fin N to Maybe (Fin M).

```agda
{-
  IsSurjective : ∀ {A B} → (A → B) → Set
  IsSurjective f = ∀ y → ∃ λ x → f x ≡ y

  Vx = Cx , but with an index for length

  BuildΔ : ∀ {N M} → (Σ (Fin N → Maybe (Fin M)) IsSurjective) → Vx ⋆ M → Vx ⋆ (M - N) → Vx ⋆ N
  BuildΔ = ?

  data ConstructSurjective : ∀ {N M} → (Σ (Fin N → Maybe (Fin M)) IsSurjective) → Set where
-}
```

```agda
{-
  module StrongerAlaMe where
    LCx : Cx ⋆ → Nat
    LCx = ?

    Injective : Nat → Nat → Set
    Injective M N = Σ (Fin M → Fin N) λ f → ∀ {x} → f x ≡ f y → x ≡ y

    data Inverse

    constructΔ : (Γ : Fin M → ⋆) (Ξ : Fin M-N → ⋆) → Cx ⋆

    M N : Nat
    _ : M ≤ N
    Γ : Cx ⋆
    _ : LCx Γ ≡ M
    Ξ : Vec ⋆ (M-N)
    f : Fin M → Fin N

    _ : ∀ {x} → f x ≡ f y → x ≡ y



    data ConstructionOfΔ (Γ : Cx ⋆) {M} (_ : LCx Γ ≡ M) ( :

    data Inj {M N : Nat}
    infix 3 _⊆_
    data _⊆_ : Cx ⋆ → Cx ⋆ → Set where
      zz : ε ⊆ ε
      zs : ∀ {Γ Δ δ} → Γ ⊆ Δ → Γ ⊆ Δ ,, δ
      ss : ∀ {Γ Δ δ} → Γ ⊆ Δ → Γ ,, δ ⊆ Δ ,, δ
-}
```

In a previous attempt at swaplemma, I said I got stuck, but was I really? I didn't try induction on Γ. I'll try again and see if I can therefore find a stronger version of a lemma.

```
    swaplemma : ∀ {Γ δ₁ δ₂ τ} Δ → τ ∈ (Γ ,, δ₁ ,, δ₂) <>< Δ → τ ∈ (Γ ,, δ₂ ,, δ₁) <>< Δ
    swaplemma [] zero = suc zero
    swaplemma [] (suc zero) = zero
    swaplemma [] (suc (suc i)) = suc (suc i)
    swaplemma {Γ} {δ₁} {δ₂} {τ} (δ ∷ Δ) i = {!!} -- I get stuck here
```


#### Chapter 3

```agda
module DependentlyTypedMetaprogramming-Chapter3 where
```

(this section not yet written)

#### Chapter 4

```agda
module DependentlyTypedMetaprogramming-Chapter4 where
```

##### functors between indexed families of sets

```agda
  open Preliminary

  record _▷_ (I J : Set) : Set₁ where
    constructor _◁_$_
    field
      ShIx : J → Set
      PoIx : (j : J) → ShIx j → Set
      riIx : (j : J) (s : ShIx j) → PoIx j s → I
    ⟦_⟧ᵢ : (I → Set) → J → Set
    ⟦_⟧ᵢ X j = Σ (ShIx j) λ s → (p : PoIx j s) → X (riIx j s p)
  open _▷_ public using (⟦_⟧ᵢ)
```

##### Functoriality (exercise 4.1)

```agda
  _⟶̇_ : ∀ {k l} {I : Set k} → (I → Set l) → (I → Set l) → Set (l ⊔ k)
  X ⟶̇ Y = ∀ i → X i → Y i

  ixMap : ∀ {I J} {C : I ▷ J} {X Y} → (X ⟶̇ Y) → ⟦ C ⟧ᵢ X ⟶̇ ⟦ C ⟧ᵢ Y
  ixMap f j xs = fst xs , f _ ∘ snd xs
```

##### Petersson-Synek Trees

```agda
  data ITree {J : Set} (C : J ▷ J) (j : J) : Set where
    ⟨_⟩ : ⟦ C ⟧ᵢ (ITree C) j → ITree C j
```

Exercise 4.2

```agda
  open DependentlyTypedMetaprogramming-Chapter2
  STLC : (Cx ⋆ × ⋆) ▷ (Cx ⋆ × ⋆)
  STLC ._▷_.ShIx (Γ , τ) = Either (τ ∈ Γ) (Either (∃ λ a → ∃ λ b → τ ≡ (a ▶ b)) ⋆)
  STLC ._▷_.PoIx (Γ , τ) (left _) = ⊥
  STLC ._▷_.PoIx (Γ , τ) (right (left _)) = Unit
  STLC ._▷_.PoIx (Γ , τ) (right (right x)) = Bool
  STLC ._▷_.riIx (Γ , τ) (left x) ()
  STLC ._▷_.riIx (Γ , .(σ ▶ τ)) (right (left (σ , τ , refl))) po = Γ ,, σ , τ
  STLC ._▷_.riIx (Γ , τ) (right (right σ)) false = Γ , σ ▶ τ
  STLC ._▷_.riIx (Γ , τ) (right (right σ)) true = Γ , σ

  stlcVar : ∀ {Γ τ} → τ ∈ Γ → ITree STLC (Γ , τ)
  stlcVar τ∈Γ = ⟨ left τ∈Γ , (λ ()) ⟩

  stlcLam : ∀ {Γ σ τ} → ITree STLC (Γ ,, σ , τ) → ITree STLC (Γ , σ ▶ τ)
  stlcLam Γ,σ⊢τ = ⟨ right (left (_ , _ , refl)) , (λ _ → Γ,σ⊢τ) ⟩

  stlcApp : ∀ {Γ σ τ} → ITree STLC (Γ , σ ▶ τ) → ITree STLC (Γ , σ) → ITree STLC (Γ , τ)
  stlcApp Γ⊢σ▶τ Γ⊢σ = ⟨ right (right _) , (λ { false → Γ⊢σ▶τ ; true → Γ⊢σ}) ⟩
```

I wonder how hard it would be to do the equivalent of "weakening" in STLC. That is, I want

```agda
  stlcWeaken : ∀ {Γ τ δ} → ITree STLC (Γ , τ) → ITree STLC (Γ ,, δ , τ)
```

Notice that none of the constructors serve this purpose directly.

In the commented-out code are three not-yet-successful attempts.

```agda
  stlcWeaken {Γ} {τ} {δ} ⟨ left τ∈Γ , _ ⟩ = ⟨ left (suc τ∈Γ) , (λ ()) ⟩
  stlcWeaken {Γ} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ = ⟨ right (left (_ , _ , refl)) , {!!} ⟩
  {-
  stlcWeaken {ε} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ with λΓ,σ⊢τ _
  stlcWeaken {ε} {.(σ ▶ σ)} {δ} ⟨ right (left (σ , .σ , refl)) , λΓ,σ⊢σ ⟩ | ⟨ left zero , _ ⟩ = ⟨ right (right δ) , (λ { false → stlcLam {!!} ; true → stlcVar zero}) ⟩
  stlcWeaken {ε} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ | ⟨ left (suc ()) , _ ⟩
  stlcWeaken {ε} {.(σ ▶ fst₁ ▶ fst₂)} {δ} ⟨ right (left (σ , .(fst₁ ▶ fst₂) , refl)) , λΓ,σ⊢τ ⟩ | ⟨ right (left (fst₁ , fst₂ , refl)) , snd₁ ⟩ = {!!}
  stlcWeaken {ε} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ | ⟨ right (right x) , snd₁ ⟩ = {!!}
  stlcWeaken {Γ ,, x} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ = {!!}
  -}
  {-
  stlcWeaken {Γ} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ =
    let Γ,δ⊢δ = stlcVar {Γ ,, δ} {δ} zero
        Γ,σ⊢τ = λΓ,σ⊢τ _
        Γ,δ,σ⊢σ = stlcVar {Γ ,, δ ,, σ} {σ} zero
        Γ,σ,δ⊢σ = stlcVar {Γ ,, σ ,, δ} {σ} (suc zero)
        Γ,δ,σ⊢δ = stlcVar {Γ ,, δ ,, σ} {δ} (suc zero)
        Γ,σ,δ⊢δ = stlcVar {Γ ,, σ ,, δ} {δ} zero
    in
    {!!} -- Γ,δ⊢σ▶τ
  -}
  {-
  stlcWeaken {Γ} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ with λΓ,σ⊢τ _
  stlcWeaken {Γ} {.(σ ▶ σ)} {δ} ⟨ right (left (σ , .σ , refl)) , λΓ,σ⊢τ ⟩ | ⟨ left zero , _ ⟩ = ⟨ right (left (_ , _ , refl)) , (λ _ → ⟨ left zero , (λ ()) ⟩) ⟩
  stlcWeaken {Γ} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ | ⟨ left (suc τ∈Γ) , _ ⟩ = ⟨ right (left (_ , _ , refl)) , (λ _ → ⟨ left (suc (suc τ∈Γ)) , (λ ()) ⟩) ⟩
  stlcWeaken {Γ} {.(σ ▶ τ₁ ▶ τ₂)} {δ} ⟨ right (left (σ , .(τ₁ ▶ τ₂) , refl)) , λΓ,σ⊢τ₁▶τ₂ ⟩ | ⟨ right (left (τ₁ , τ₂ , refl)) , λΓ,σ,τ₁⊢τ₂ ⟩ = ⟨ right (left (_ , _ , refl)) , (λ _ → {!!}) ⟩
  stlcWeaken {Γ} {.(σ ▶ τ)} {δ} ⟨ right (left (σ , τ , refl)) , λΓ,σ⊢τ ⟩ | ⟨ right (right x) , snd₁ ⟩ = {!!} -- ⟨ right (left (_ , _ , refl)) , (λ _ → {!!}) ⟩
  -}
  stlcWeaken {Γ} {τ} {δ} ⟨ right (right x) , r ⟩ with r true | r false
  ... | Γ⊢x | Γ⊢x▶τ =
    let Γ,δ⊢x = stlcWeaken {δ = δ} Γ⊢x
        Γ,δ⊢x▶τ = stlcWeaken {δ = δ} Γ⊢x▶τ
    in
    {!stlcApp Γ,δ⊢x▶τ Γ,δ⊢x!} -- type-checks but does not terminate-check
```

At least I have convinced myself that `stlcWeaken` is as hard a problem (for me) as `WeakenAlphabetFrom`.

#### Chapter 5

```agda
module DependentlyTypedMetaprogramming-Chapter5 where
```

(this section not yet written)

#### Chapter 6

```agda
module DependentlyTypedMetaprogramming-Chapter6 where
```

(this section not yet written)

### The Metaprogrammatic "softcore" Solution to the `Hardcore.Alphabet` problem

(this section not yet written)

### Some more experiments and scribblings

#### A fresh "Preliminary"

```agda
module Preliminary-Experiment where

  open import Prelude public
  open import Tactic.Nat public

  add-zero : ∀ n → n ≡ n +N 0
  add-zero zero = refl
  add-zero (suc n) = cong suc (add-zero n)

  add-suc : ∀ n m → n +N suc m ≡ suc n +N m
  add-suc zero m = refl
  add-suc (suc n) m = cong suc (add-suc n m)

  ∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃_ = Σ _

  record _▷_ (I J : Set) : Set₁ where
    constructor _◁_$_
    field
      ShIx : J → Set
      PoIx : (j : J) → ShIx j → Set
      riIx : (j : J) (s : ShIx j) → PoIx j s → I
    ⟦_⟧ᵢ : (I → Set) → J → Set
    ⟦_⟧ᵢ X j = Σ (ShIx j) λ s → (p : PoIx j s) → X (riIx j s p)
  open _▷_ public using (⟦_⟧ᵢ)

  wkFinFrom : ∀ {N} → Fin (suc N) → Fin N → Fin (suc N)
  wkFinFrom zero x = suc x
  wkFinFrom (suc from) zero = zero
  wkFinFrom (suc from) (suc x) = suc (wkFinFrom from x)

  wkFinByFrom : ∀ {N} (by : Nat) → Fin (suc N) → Fin N → Fin (by + N)
  wkFinByFrom zero from x = x
  wkFinByFrom (suc by) from x = transport Fin (add-suc by _) (wkFinByFrom by (suc from) (wkFinFrom from x))


  -- eliminate an occurrence of iₓ within iᵥ, shifting down everything above iₓ
  -- given a (v : var iₓ), returns the index of v[iᵥ/iₓ]
  sbFin : ∀ {N} {iₓ iᵥ : Fin (suc N)} → (iₓ ≡ iᵥ → ⊥) → Fin N
  sbFin         {iₓ = zero  } {zero}   z≢z     = ⊥-elim (z≢z refl)
  sbFin         {iₓ = zero  } {suc iᵥ} _       = iᵥ
  sbFin {zero}  {     suc ()} {zero}   _
  sbFin {suc N} {     suc iₓ} {zero}   _       = zero
  sbFin {zero}  {     suc ()} {suc iᵥ} _
  sbFin {suc N} {     suc iₓ} {suc iᵥ} siₓ≢siᵥ = suc (sbFin {iₓ = iₓ} {iᵥ} λ {refl → siₓ≢siᵥ refl})

  _⟶̇_ : ∀ {k l} {I : Set k} → (I → Set l) → (I → Set l) → Set (l ⊔ k)
  X ⟶̇ Y = ∀ i → X i → Y i

  ixMap : ∀ {I J} {C : I ▷ J} {X Y} → (X ⟶̇ Y) → ⟦ C ⟧ᵢ X ⟶̇ ⟦ C ⟧ᵢ Y
  ixMap f j xs = fst xs , f _ ∘ snd xs

  data ITree {J : Set} (C : J ▷ J) (j : J) : Set where
    ⟨_⟩ : ⟦ C ⟧ᵢ (ITree C) j → ITree C j

  data Desc {l} (I : Set l) : Set (lsuc l) where
    var : I → Desc I
    σ π : (A : Set l) (D : A → Desc I) → Desc I
    _×ᴰ_ : Desc I → Desc I → Desc I
    κ : Set l → Desc I
  infixr 4 _×ᴰ_

  ⟦_⟧ᴰ : ∀ {l} {I : Set l} → Desc I → (I → Set l) → Set l
  ⟦ var i ⟧ᴰ X = X i
  ⟦ σ A D ⟧ᴰ X = Σ A λ a → ⟦ D a ⟧ᴰ X
  ⟦ π A D ⟧ᴰ X = (a : A) → ⟦ D a ⟧ᴰ X
  ⟦ D ×ᴰ E ⟧ᴰ X = ⟦ D ⟧ᴰ X × ⟦ E ⟧ᴰ X
  ⟦ κ A ⟧ᴰ X = A

  data Data {l} {J : Set l} (F : J → Desc J) (j : J) : Set l where
    ⟨_⟩ : ⟦ F j ⟧ᴰ (Data F) → Data F j
```

#### A go at trying to solve the problem "from scratch" with some custom meta-programming

It turns out I still have a problem with proving termination, even with a vastly different approach.

```agda
module ExperimentWithCustomMeta where
  open Preliminary-Experiment

  -- the thing I want to model
  data MyTerm (N : Nat) : Set where
    var : Fin N → MyTerm N -- there can be only one of these (Variable)
    universe : Nat → MyTerm N -- there can be only one of these (Universe)
    -- here are a few of these (Function)
    ΠF : MyTerm N → MyTerm (suc N) → MyTerm N
    ΠI : MyTerm (suc N) → MyTerm N
    ΠE : MyTerm N → MyTerm N → MyTerm N
    -- ... and there are possibly many other such constructors

  data FunctionBinders
    (Nat' : Set) (add' : Nat' → Nat' → Nat') -- a monoid
    (Target : Nat' → Set) -- indexed by the monoid
    (N : Nat') -- current index
    : {#FA : Nat} → Vec Nat' #FA → Set where
    [] : FunctionBinders Nat' add' Target N []
    _∷_ : ∀ {#fa binding} {bindings : Vec Nat' #fa}
        → Target (add' binding N)
        → FunctionBinders Nat' add' Target N bindings
        → FunctionBinders Nat' add' Target N (binding ∷ bindings)

  module _
    (Target : Nat → Set)
    where

    Variable : Set
    Variable = {N : Nat} → Fin N → Target N

    Universe : Set
    Universe = {N : Nat} → Nat → Target N

    infix 2 _↠_
    record Function : Set where
      constructor _↠_
      field
        {#FA} : Nat
        binding : Vec Nat #FA
        function : {N : Nat} → FunctionBinders Nat _+_ Target N binding → Target N

    infix 1 _/_∣_
    record NatModel : Set where
      constructor _/_∣_
      field
        vari : Variable
        univ : Universe
        {#F} : Nat
        funs : Vec Function #F
      getFunction : Fin #F → Function
      getFunction #f = indexVec funs #f


    data AsData (m : NatModel) (N : Nat) : Set
    data AsBound (m : NatModel) (N : Nat) : {#arity : Nat} → Vec Nat #arity → Set

    data AsData (m : NatModel) (N : Nat) where
      var : Fin N → AsData m N
      uni : Nat → AsData m N
      fun : (#f : Fin (NatModel.#F m))
          → (let thefun = NatModel.getFunction m #f)
          → (let #fa = Function.#FA thefun)
          → (let binding = Function.binding thefun)
          → AsBound m N binding -- interpretBindings (AsData m) binding N
          → AsData m N

    data AsBound (m : NatModel) (N : Nat) where
      [] : AsBound m N []
      _∷_ : ∀ {n binding} → AsData m (binding + N) → {bindings : Vec Nat n} → AsBound m N bindings → AsBound m N (binding ∷ bindings)

{-
    interpretBindings :
      (X : Nat → Set)
      {#fa : Nat}
      (binding : Vec Nat #fa)
      (N : Nat)
      → Set
    interpretBindings X [] _ = ⊤
    interpretBindings X (binding ∷ bindings) N = X (binding + N) × interpretBindings X bindings N
-}
{-
    data AsData (m : NatModel) (N : Nat) : Set where
      var : Fin N → AsData m N
      uni : Nat → AsData m N
      fun : (#f : Fin (NatModel.#F m))
          → (let thefun = NatModel.getFunction m #f)
          → (let #fa = Function.#FA thefun)
          → (let binding = Function.binding thefun)
          → interpretBindings (AsData m) binding N
          → AsData m N
-}
    realiseData : (m : NatModel) {N : Nat} → AsData m N → Target N
    realiseFunctionBinders : ∀ {N} (m : NatModel)
                               {#FA : Nat} (binding : Vec Nat #FA) →
                             AsBound m N binding →
                             FunctionBinders Nat _+_ Target N binding

    realiseData (vari / univ ∣ funs) (var x) = vari x
    realiseData (vari / univ ∣ funs) (uni x) = univ x
    realiseData m@(vari / univ ∣ funs) (fun #f x) = Function.function (indexVec funs #f) (realiseFunctionBinders m (indexVec funs #f .Function.binding) x)

    realiseFunctionBinders (vari / univ ∣ funs) [] x = []
    realiseFunctionBinders m (binding ∷ bindings) (d ∷ x) = realiseData m d ∷ realiseFunctionBinders m bindings x

    weakenTargetByFrom : (m : NatModel) → (by : Nat) {N : Nat} → (from : Fin (suc N)) → AsData m N → AsData m (by + N)
    weakenBindingsByFrom : (m : NatModel) {#fa : Nat} (binding : Vec Nat #fa) → (by : Nat)  {N : Nat} → (from : Fin (suc N)) → AsBound m N binding → AsBound m (by + N) binding

    weakenTargetByFrom (vari / univ ∣ funs) by from (var x) = var (wkFinByFrom by from x)
    weakenTargetByFrom (vari / univ ∣ funs) by from (uni x) = uni x
    weakenTargetByFrom m@(vari / univ ∣ funs) by from (fun z x) = fun z (weakenBindingsByFrom m _ by from x)

    weakenBindingsByFrom m [] by from x = []
    weakenBindingsByFrom m (binding ∷ bindings) by {N} from (d ∷ ib) =
      let
        from' : Fin (suc (binding + N))
        from' = transport Fin auto $ wkFinByFrom binding zero from
      in (transport (AsData m) auto $ weakenTargetByFrom m by from' d) ∷ weakenBindingsByFrom m _ by from ib

    {-# TERMINATING #-}
    instantiateVariableAt : (m : NatModel)
      → ∀ {N} → Fin (suc N) → AsData m N → AsData m (suc N) → AsData m N
    instantiateBindingsAt : (m : NatModel)
      → ∀ {N} → Fin (suc N) → {#fa : Nat} {binding : Vec Nat #fa}
      → AsData m N
      → AsBound m (suc N) binding
      → AsBound m N binding


    instantiateVariableAt m at ρ (var x) with at == x
    ... | yes _ = ρ
    ... | no at≢x = var (sbFin at≢x)
    instantiateVariableAt m at ρ (uni x) = uni x
    instantiateVariableAt m at ρ (fun #f x) = fun #f (instantiateBindingsAt m at ρ x)

    instantiateBindingsAt m at {binding = []} ρ b = []
    instantiateBindingsAt m at {binding = binding ∷ bindings} ρ (d ∷ ibs) = instantiateVariableAt m (transport Fin auto (wkFinByFrom binding zero at)) (weakenTargetByFrom m binding zero ρ) (transport (AsData m) auto d) ∷ instantiateBindingsAt m at ρ ibs

    cVar : NatModel → {N : Nat} → Fin N → Target N
    cVar = NatModel.vari

    -- data InhabitantOfNatModel : Set where

  modeled : NatModel MyTerm
  modeled =
    var /
    universe ∣
    (0 ∷ 1 ∷ [] ↠ λ { (x₁ ∷ x₂ ∷ []) → ΠF x₁ x₂}) ∷
    (    1 ∷ [] ↠ λ { (x₁ ∷      []) → ΠI x₁   }) ∷
    (0 ∷ 0 ∷ [] ↠ λ { (x₁ ∷ x₂ ∷ []) → ΠE x₁ x₂}) ∷
    []

  test1 : AsData MyTerm modeled 3
  test1 = fun 0 (uni 27 ∷ fun 0 (var 1 ∷ var 3 ∷ []) ∷ [])

  test1-weakened : AsData MyTerm modeled 4
  test1-weakened = weakenTargetByFrom MyTerm modeled 1 1 test1

  realised : MyTerm _
  realised = realiseData MyTerm modeled test1-weakened

  substituted : AsData MyTerm modeled 3
  substituted = instantiateVariableAt MyTerm modeled 0 test1 test1-weakened

  data Grammar : Set where
    variable : Grammar
    universe : Grammar
    term : ∀ {arity} → Vec Nat arity → Grammar

{-
  recursor : (Languages : List LANGUAGE) → Nat → (Nat → Set) → Set
  recursor' : (Languages : List Nat) → Nat → (Nat → Set) → Set
-}
{-
  recursor [] N X = ⊤
  recursor (universe ∷ Languages) N X = Either Nat (recursor Languages N X)
  recursor (variable ∷ Languages) N X = Either (Fin N) (recursor Languages N X)
  recursor (term bs ∷ Languages) N X = Either (recursor' bs N X) (recursor Languages N X)

  recursor' [] N X = ⊤
  recursor' (b ∷ bs) N X = X (b + N) × recursor' bs N X

  data TERM (Languages : List LANGUAGE) (N : Nat) : Set where
    recurse : recursor Languages N (TERM Languages) → TERM Languages N

  wkTERM : {Languages : List LANGUAGE} {N : Nat} → (by : Nat) (from : Fin (suc N)) → TERM Languages N → TERM Languages (by + N)
  wkTERM {[]} by from (recurse x) = recurse x
  wkTERM {universe ∷ Languages} by from (recurse (left x)) = recurse (left x)
  wkTERM {universe ∷ Languages} by from (recurse (right x)) = wkTERM by from {!!}
  wkTERM {variable ∷ Languages} by from (recurse x) = {!!}
  wkTERM {term x₁ ∷ Languages} by from (recurse x) = {!!}
-}
```

#### Trying again, but turning parameters into indices

This will hopefully solve the problem with termination. Related agda issue: #2527

```agda
module IndexedAllTheWay where
  open Preliminary-Experiment

  module _
    (Target : Nat → Set)
    where

    data FunctionBinders

      : (N : Nat) {#FA : Nat} → Vec Nat #FA → Set where
      [] : {N : Nat} → FunctionBinders N []
      _∷_ : ∀ {N : Nat} {#fa binding} {bindings : Vec Nat #fa}
          → Target (binding + N)
          → FunctionBinders N bindings
          → FunctionBinders N (binding ∷ bindings)

    Variable : Set
    Variable = {N : Nat} → Fin N → Target N

    infix 2 _↠_
    record Function : Set where
      constructor _↠_
      field
        {#FA} : Nat
        binding : Vec Nat #FA
        function : {N : Nat} → FunctionBinders N binding → Target N

    record NatModel : Set where
      field
        vari : Variable
        {#F} : Nat
        funs : Vec Function #F
      getFunction : Fin #F → Function
      getFunction #f = indexVec funs #f

    module _ (m : NatModel) where

      data AsData : (N : Nat) → Set
      data AsBound : (N : Nat) → {#arity : Nat} → Vec Nat #arity → Set

      data AsData {-(N : Nat)-} where
        var : {N : Nat} → Fin N → AsData N
        uni : {N : Nat} → Nat → AsData N
        fun : {N : Nat} → (#f : Fin (NatModel.#F m))
            → (let thefun = NatModel.getFunction m #f)
            → (let #fa = Function.#FA thefun)
            → (let binding = Function.binding thefun)
            → AsBound N binding
            → AsData N

      data AsBound {-(N : Nat)-} where
        [] : {N : Nat} → AsBound N []
        _∷_ : {N : Nat} → ∀ {n binding} → AsData (binding + N) → {bindings : Vec Nat n} → AsBound N bindings → AsBound N (binding ∷ bindings)

      weakenTargetByFrom : (by : Nat) {N : Nat} → (from : Fin (suc N)) → AsData N → AsData (by + N)
      weakenBindingsByFrom : {#fa : Nat} (binding : Vec Nat #fa) → (by : Nat)  {N : Nat} → (from : Fin (suc N)) → AsBound N binding → AsBound (by + N) binding

      weakenTargetByFrom by from (var x) = var (wkFinByFrom by from x)
      weakenTargetByFrom by from (uni x) = uni x
      weakenTargetByFrom by from (fun z x) = fun z (weakenBindingsByFrom _ by from x)

      weakenBindingsByFrom [] by from x = []
      weakenBindingsByFrom (binding ∷ bindings) by {N} from (d ∷ ib) =
        let
          from' : Fin (suc (binding + N))
          from' = transport Fin auto $ wkFinByFrom binding zero from
        in (transport AsData auto $ weakenTargetByFrom by from' d) ∷ weakenBindingsByFrom _ by from ib

      {-# TERMINATING #-}
      instantiateVariableAt : ∀ {N} → Fin (suc N) → AsData N → AsData (suc N) → AsData N
      instantiateBindingsAt : ∀ {N} → Fin (suc N) → {#fa : Nat} {binding : Vec Nat #fa}
        → AsData N
        → AsBound (suc N) binding
        → AsBound N binding

      instantiateVariableAt at ρ (var x) with at == x
      ... | yes _ = ρ
      ... | no at≢x = var (sbFin at≢x)
      instantiateVariableAt at ρ (uni x) = uni x
      instantiateVariableAt at ρ (fun #f x) = fun #f (instantiateBindingsAt at ρ x)

      instantiateBindingsAt at {binding = []} ρ b = []
      instantiateBindingsAt at {binding = binding ∷ bindings} ρ (d ∷ ibs) = instantiateVariableAt (transport Fin auto (wkFinByFrom binding zero at)) (weakenTargetByFrom binding zero ρ) (transport AsData auto d) ∷ instantiateBindingsAt at ρ ibs
```

Well, it doesn't solve it. So, on to debugging: the following will try to replicate the problem in simplified form.

```agda
module SimplifiedTerminationProblem where
  open Preliminary-Experiment

  module _
    (Target : Nat → Set)
    where

    data FunctionBinders

      : (N : Nat) (#FA : Nat) → Set where
      [] : {N : Nat} → FunctionBinders N 0
      _∷_ : ∀ {N : Nat} {#fa}
          → Target N
          → FunctionBinders N #fa
          → FunctionBinders N (suc #fa)

    Variable : Set
    Variable = {N : Nat} → Fin N → Target N

    infix 2 _↠_
    record Function : Set where
      constructor _↠_
      field
        #FA : Nat
        function : {N : Nat} → FunctionBinders N #FA → Target N

    record NatModel : Set where
      field
        vari : Variable
        {#F} : Nat
        funs : Vec Function #F
      getFunction : Fin #F → Function
      getFunction #f = indexVec funs #f

    module _ (m : NatModel) where

      data AsData : (N : Nat) → Set
      data AsBound : (N : Nat) → (#arity : Nat) → Set

      data AsData where
        var : {N : Nat} → Fin N → AsData N
        uni : {N : Nat} → Nat → AsData N
        fun : {N : Nat} → (#f : Fin (NatModel.#F m))
            → (let thefun = NatModel.getFunction m #f)
            → (let #fa = Function.#FA thefun)
            → AsBound N #fa
            → AsData N

      data AsBound where
        [] : {N : Nat} → AsBound N 0
        _∷_ : {N : Nat} → ∀ {n} → AsData N → AsBound N n → AsBound N (suc n)

      postulate
        weakenTargetByFrom : {N : Nat} → (from : Fin (suc N)) → AsData N → AsData N

      {-# TERMINATING #-}
      instantiateVariableAt : ∀ {N} → Fin (suc N) → AsData N → AsData (suc N) → AsData N
      instantiateBindingsAt : ∀ {N} → Fin (suc N) → {#fa : Nat}
        → AsData N
        → AsBound (suc N) #fa
        → AsBound N #fa

      instantiateVariableAt at ρ (var x) with at == x
      ... | yes _ = ρ
      ... | no at≢x = var (sbFin at≢x)
      instantiateVariableAt at ρ (uni x) = uni x
      instantiateVariableAt at ρ (fun #f x) = fun #f (instantiateBindingsAt at ρ x)

      instantiateBindingsAt at {0} ρ b = []
      instantiateBindingsAt at {suc n} ρ (d ∷ ibs) = instantiateVariableAt ((wkFinByFrom zero zero at)) (weakenTargetByFrom zero ρ)
        (transport AsData refl d) -- change this to `d` and there is no termination problem
        ∷ instantiateBindingsAt at ρ ibs
```

From the above, I see that the use of `transport` is causing the termination check to fail.

The next step goes back to the version where I used indexes instead of parameters and tries to fix the problem by using rewrite instead of transport.

```agda
module RewriteInsteadOfTransport where
  open Preliminary-Experiment

  module _
    (Target : Nat → Set)
    where

    data FunctionBinders

      : (N : Nat) {#FA : Nat} → Vec Nat #FA → Set where
      [] : {N : Nat} → FunctionBinders N []
      _∷_ : ∀ {N : Nat} {#fa binding} {bindings : Vec Nat #fa}
          → Target (binding + N)
          → FunctionBinders N bindings
          → FunctionBinders N (binding ∷ bindings)

    Variable : Set
    Variable = {N : Nat} → Fin N → Target N

    infix 2 _↠_
    record Function : Set where
      constructor _↠_
      field
        {#FA} : Nat
        binding : Vec Nat #FA
        function : {N : Nat} → FunctionBinders N binding → Target N

    record NatModel : Set where
      field
        vari : Variable
        {#F} : Nat
        funs : Vec Function #F
      getFunction : Fin #F → Function
      getFunction #f = indexVec funs #f

    module _ (m : NatModel) where

      data AsData : (N : Nat) → Set
      data AsBound : (N : Nat) → {#arity : Nat} → Vec Nat #arity → Set

      data AsData {-(N : Nat)-} where
        var : {N : Nat} → Fin N → AsData N
        uni : {N : Nat} → Nat → AsData N
        fun : {N : Nat} → (#f : Fin (NatModel.#F m))
            → (let thefun = NatModel.getFunction m #f)
            → (let #fa = Function.#FA thefun)
            → (let binding = Function.binding thefun)
            → AsBound N binding
            → AsData N

      data AsBound {-(N : Nat)-} where
        [] : {N : Nat} → AsBound N []
        _∷_ : {N : Nat} → ∀ {n binding} → AsData (binding + N) → {bindings : Vec Nat n} → AsBound N bindings → AsBound N (binding ∷ bindings)

      weakenTargetByFrom : (by : Nat) {N : Nat} → (from : Fin (suc N)) → AsData N → AsData (by + N)
      weakenBindingsByFrom : {#fa : Nat} (binding : Vec Nat #fa) → (by : Nat)  {N : Nat} → (from : Fin (suc N)) → AsBound N binding → AsBound (by + N) binding

      weakenTargetByFrom by from (var x) = var (wkFinByFrom by from x)
      weakenTargetByFrom by from (uni x) = uni x
      weakenTargetByFrom by from (fun z x) = fun z (weakenBindingsByFrom _ by from x)

      weakenBindingsByFrom [] by from x = []
      weakenBindingsByFrom (binding ∷ bindings) by {N} from (d ∷ ib) =
        let
          from' : Fin (suc (binding + N))
          from' = transport Fin auto $ wkFinByFrom binding zero from
        in (transport AsData auto $ weakenTargetByFrom by from' d) ∷ weakenBindingsByFrom _ by from ib

      instantiateVariableAt : ∀ {N} → Fin (suc N) → AsData N → AsData (suc N) → AsData N
      instantiateBindingsAt : ∀ {N} → Fin (suc N) → {#fa : Nat} {binding : Vec Nat #fa}
        → AsData N
        → AsBound (suc N) binding
        → AsBound N binding

      instantiateVariableAt at ρ (var x) with at == x
      ... | yes _ = ρ
      ... | no at≢x = var (sbFin at≢x)
      instantiateVariableAt at ρ (uni x) = uni x
      instantiateVariableAt at ρ (fun #f x) = fun #f (instantiateBindingsAt at ρ x)

      instantiateBindingsAt at {binding = []} ρ b = []
      instantiateBindingsAt {N} at {binding = binding ∷ bindings} ρ (d ∷ ibs) rewrite (auto ofType binding + suc N ≡ suc (binding + N)) = instantiateVariableAt (transport Fin auto (wkFinByFrom binding zero at)) (weakenTargetByFrom binding zero ρ) d ∷ instantiateBindingsAt at ρ ibs
```

Yup, that fixes it. Now, back to the parameterised version.

```agda
module ParameterisedWithRewrite where
  open Preliminary-Experiment

  -- the thing I want to model
  data MyTerm (N : Nat) : Set where
    var : Fin N → MyTerm N -- there can be only one of these (Variable)
    universe : Nat → MyTerm N -- there can be only one of these (Universe)
    -- here are a few of these (Function)
    ΠF : MyTerm N → MyTerm (suc N) → MyTerm N
    ΠI : MyTerm (suc N) → MyTerm N
    ΠE : MyTerm N → MyTerm N → MyTerm N
    -- ... and there are possibly many other such constructors

  data FunctionBinders
    (Nat' : Set) (add' : Nat' → Nat' → Nat') -- a monoid
    (Target : Nat' → Set) -- indexed by the monoid
    (N : Nat') -- current index
    : {#FA : Nat} → Vec Nat' #FA → Set where
    [] : FunctionBinders Nat' add' Target N []
    _∷_ : ∀ {#fa binding} {bindings : Vec Nat' #fa}
        → Target (add' binding N)
        → FunctionBinders Nat' add' Target N bindings
        → FunctionBinders Nat' add' Target N (binding ∷ bindings)

  module _
    (Target : Nat → Set)
    where

    Variable : Set
    Variable = {N : Nat} → Fin N → Target N

    Universe : Set
    Universe = {N : Nat} → Nat → Target N

    infix 2 _↠_
    record Function : Set where
      constructor _↠_
      field
        {#FA} : Nat
        binding : Vec Nat #FA
        function : {N : Nat} → FunctionBinders Nat _+_ Target N binding → Target N

    infix 1 _/_∣_
    record NatModel : Set where
      constructor _/_∣_
      field
        vari : Variable
        univ : Universe
        {#F} : Nat
        funs : Vec Function #F
      getFunction : Fin #F → Function
      getFunction #f = indexVec funs #f

    data AsData (m : NatModel) (N : Nat) : Set
    data AsBound (m : NatModel) (N : Nat) : {#arity : Nat} → Vec Nat #arity → Set

    data AsData (m : NatModel) (N : Nat) where
      var : Fin N → AsData m N
      uni : Nat → AsData m N
      fun : (#f : Fin (NatModel.#F m))
          → (let thefun = NatModel.getFunction m #f)
          → (let #fa = Function.#FA thefun)
          → (let binding = Function.binding thefun)
          → AsBound m N binding
          → AsData m N

    data AsBound (m : NatModel) (N : Nat) where
      [] : AsBound m N []
      _∷_ : ∀ {n binding} → AsData m (binding + N) → {bindings : Vec Nat n} → AsBound m N bindings → AsBound m N (binding ∷ bindings)

    realiseData : (m : NatModel) {N : Nat} → AsData m N → Target N
    realiseFunctionBinders : ∀ {N} (m : NatModel)
                               {#FA : Nat} (binding : Vec Nat #FA) →
                             AsBound m N binding →
                             FunctionBinders Nat _+_ Target N binding

    realiseData (vari / univ ∣ funs) (var x) = vari x
    realiseData (vari / univ ∣ funs) (uni x) = univ x
    realiseData m@(vari / univ ∣ funs) (fun #f x) = Function.function (indexVec funs #f) (realiseFunctionBinders m (indexVec funs #f .Function.binding) x)

    realiseFunctionBinders (vari / univ ∣ funs) [] x = []
    realiseFunctionBinders m (binding ∷ bindings) (d ∷ x) = realiseData m d ∷ realiseFunctionBinders m bindings x

    weakenTargetByFrom : (m : NatModel) → (by : Nat) {N : Nat} → (from : Fin (suc N)) → AsData m N → AsData m (by + N)
    weakenBindingsByFrom : (m : NatModel) {#fa : Nat} (binding : Vec Nat #fa) → (by : Nat)  {N : Nat} → (from : Fin (suc N)) → AsBound m N binding → AsBound m (by + N) binding

    weakenTargetByFrom (vari / univ ∣ funs) by from (var x) = var (wkFinByFrom by from x)
    weakenTargetByFrom (vari / univ ∣ funs) by from (uni x) = uni x
    weakenTargetByFrom m@(vari / univ ∣ funs) by from (fun z x) = fun z (weakenBindingsByFrom m _ by from x)

    weakenBindingsByFrom m [] by from x = []
    weakenBindingsByFrom m (binding ∷ bindings) by {N} from (d ∷ ib) =
      let
        from' : Fin (suc (binding + N))
        from' = transport Fin auto $ wkFinByFrom binding zero from
      in (transport (AsData m) auto $ weakenTargetByFrom m by from' d) ∷ weakenBindingsByFrom m _ by from ib

    instantiateVariableAt : (m : NatModel)
      → ∀ {N} → Fin (suc N) → AsData m N → AsData m (suc N) → AsData m N
    instantiateBindingsAt : (m : NatModel)
      → ∀ {N} → Fin (suc N) → {#fa : Nat} {binding : Vec Nat #fa}
      → AsData m N
      → AsBound m (suc N) binding
      → AsBound m N binding


    instantiateVariableAt m at ρ (var x) with at == x
    ... | yes _ = ρ
    ... | no at≢x = var (sbFin at≢x)
    instantiateVariableAt m at ρ (uni x) = uni x
    instantiateVariableAt m at ρ (fun #f x) = fun #f (instantiateBindingsAt m at ρ x)

    instantiateBindingsAt m at {binding = []} ρ b = []
    instantiateBindingsAt m {N} at {binding = binding ∷ bindings} ρ (d ∷ ibs) rewrite (auto ofType binding + suc N ≡ suc (binding + N)) = instantiateVariableAt m (transport Fin auto (wkFinByFrom binding zero at)) (weakenTargetByFrom m binding zero ρ) d ∷ instantiateBindingsAt m at ρ ibs

  modeled : NatModel MyTerm
  modeled =
    var /
    universe ∣
    (0 ∷ 1 ∷ [] ↠ λ { (x₁ ∷ x₂ ∷ []) → ΠF x₁ x₂}) ∷
    (    1 ∷ [] ↠ λ { (x₁ ∷      []) → ΠI x₁   }) ∷
    (0 ∷ 0 ∷ [] ↠ λ { (x₁ ∷ x₂ ∷ []) → ΠE x₁ x₂}) ∷
    []

  test1 : AsData MyTerm modeled 3
  test1 = fun 0 (uni 27 ∷ fun 0 (var 1 ∷ var 3 ∷ []) ∷ [])

  test1-weakened : AsData MyTerm modeled 4
  test1-weakened = weakenTargetByFrom MyTerm modeled 1 1 test1

  realised : MyTerm _
  realised = realiseData MyTerm modeled test1-weakened

  substituted : AsData MyTerm modeled 3
  substituted = instantiateVariableAt MyTerm modeled 0 test1 test1-weakened
```

#### just some scribbles

```agda
module Outline2 where
  open Preliminary-Experiment

  #Binder = Nat
  #FV = Nat

  data Grammar : Set where
    universe variable : Grammar
    function : ∀ {N} → Vec #Binder N → Grammar

  Language : Set₁
  Language = Grammar → Set

  Symbol : Language → Set
  Symbol l = Σ Grammar l

  Context = Nat
```

How to talk about variables?

() ⊢ ΠF (𝒰 ℓ) (𝓋 0) is valid because 0 refers to a variable in context (in this case, it's the one bound by ΠF's first component.

(x : Anything) ⊢ ΠF (𝒰 ℓ) (𝓋 1) is valid because 1 refers to the variable x.

I want to perform operations on well-scoped terms involving variables, such as weakening and substitution, *and* be guaranteed that ... what? It's easy enough to guarantee that the terms are well-scoped, if we parameterise by the number of contextual elements. When we weaken a term τ by prefixing one place to it, we want if Γ ⊢ τ, then Γ , σ ⊢ τ. for some context Γ : Context N

Perhaps we want to say

weaken :
  Γ ⊢ τ ∶ Τ → Γ ,,  ⊢

τ : WellScopedInContextOfSize N
------------------------------------------------------
wk τ : WellScopedInContextOfSize (suc N)

τ : WellScopedInContextOfSize (suc N)    ρ : WellScopedInContextOfSize N    n : Nat< N
---------------------------------------------------------------------------------------
sub ρ n τ : WellScopedInContextOfSize N

i.e. build up WellScoped N similar to Term N but by including renaming and substitution as constructors.

But then we need a way to convert WellScoped N to Term N, with some guarantee about it being done correctly.

#### scribbling about variables

```agda
module Scratch2 where
  open Preliminary-Experiment
  data Cx : Set where
    ε : Cx
    _,,_ : Cx → Nat → Cx
  infixl 5 _,,_
  infix 3 _∈_
  data _∈_ (τ : Nat) : Cx → Set where
    zero : ∀ {Γ} → τ ∈ Γ ,, τ
    suc : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ ,, σ
  infix 3 _⊢_
  data _⊢_ (Γ : Cx) : Nat → Set where
    var : ∀ {τ} → τ ∈ Γ → Γ ⊢ τ
    -- lam : ∀ {σ τ} → Γ ,, suc τ ⊢ τ → Γ ⊢ τ -- ????????
```

#### A go at using indexed containers to solve the problem, but finding an issue with termination

```agda
module Outline where
  open Preliminary-Experiment

  #Binder = Nat
  #FV = Nat

  data Grammar : Set where
    universe variable : Grammar
    term : ∀ {N} → Vec #Binder N → Grammar

  Symbol : Set₁
  Symbol = Grammar → Set

  Letter : Symbol → Set
  Letter symbol = Σ Grammar symbol

  Clause : Symbol → Set
  Clause symbol = Letter symbol × #FV

  data Universe : Set where
    ⋆ : Universe
    ↑ : Universe → Universe

  termD : {S : Symbol} → Clause S → Desc (Clause S)
  termD ((universe , 𝓊) , #fv) = κ Universe
  termD ((variable , 𝓋) , #fv) = κ (Fin #fv)
  termD {S} ((term {#arity} binders , 𝓉) , #fv) = σ (Vec (∃ S) #arity) λ s → π (Fin #arity) λ p → var (indexVec s p , indexVec binders p + #fv)

  termC : (S : Symbol) → Clause S ▷ Clause S

  termC _ ._▷_.ShIx ((universe        , _) , _  ) = Universe
  termC _ ._▷_.ShIx ((variable        , _) , #fv) = Fin #fv
  termC S ._▷_.ShIx ((term {#arity} _ , _) , _  ) = Vec (∃ S) #arity

  termC _ ._▷_.PoIx ((universe        , _) , _  ) _ = ⊥
  termC _ ._▷_.PoIx ((variable        , _) , _  ) _ = ⊥
  termC _ ._▷_.PoIx ((term {#arity} _ , _) , _  ) _ = Fin #arity

  termC _ ._▷_.riIx ((universe        , _) , _  ) _   ()
  termC _ ._▷_.riIx ((variable        , _) , _  ) _   ()
  termC _ ._▷_.riIx ((term binders    , y) , #fv) gys i  = indexVec gys i , indexVec binders i + #fv

  wkFin : ∀ {N} → Fin N → Fin (suc N)
  wkFin = suc

  wkClause : {S : Symbol} → Clause S → Clause S
  wkClause (gy , #fv) = gy , 1 + #fv

  wkClauseBy : {S : Symbol} → Nat → Clause S → Clause S
  wkClauseBy by (gy , #fv) = gy , by + #fv

  wkITermByFrom : {S : Symbol} {c : Clause S} (by : Nat) (from : Fin (suc (snd c))) → ITree (termC S) c → ITree (termC S) (wkClauseBy by c)
  wkITermByFrom {c = (universe , _) , _} _ _ ⟨ ℓ , _ ⟩ = ⟨ ℓ , (λ ()) ⟩
  wkITermByFrom {c = (variable , s) , #fv} by from ⟨ v , _ ⟩ = ⟨ wkFinByFrom by from v , (λ ()) ⟩
  wkITermByFrom {c = (term binders , s) , #fv} by from ⟨ gys , r ⟩ = ⟨ gys , (λ p → transport (λ z → ITree (termC _) (indexVec gys p , z)) auto (wkITermByFrom by (transport Fin (add-suc (indexVec binders p) #fv) (wkFinByFrom (indexVec binders p) zero from)) (r p))) ⟩

  Term : Symbol → #FV → Set
  Term S #fv = Σ (Letter S) λ l → ITree (termC S) (l , #fv)

  wkTermByFrom : {S : Symbol} {#fv : #FV} (by : Nat) (from : Fin (suc #fv)) → Term S #fv → Term S (by + #fv)
  wkTermByFrom by from (l , τ) = l , wkITermByFrom by from τ

  wkTerm : {S : Symbol} {#fv : #FV} → Term S #fv → Term S (suc #fv)
  wkTerm t = wkTermByFrom 1 0 t

  module SampleTest where -- to see that we can convert the indexed representation back to a "normal" form

    data SampleSymbol : Symbol where
      𝒰 : SampleSymbol universe
      𝓋 : SampleSymbol variable
      Π : SampleSymbol (term (0 ∷ 1 ∷ []))

    sampleTermD : Data (termD {SampleSymbol}) ((_ , Π) , 1)
    sampleTermD = ⟨ (_ , 𝓋) ∷ (_ , 𝓋) ∷ [] , (λ { zero → ⟨ 0 ⟩ ; (suc zero) → ⟨ 0 ⟩ ; (suc (suc ()))}) ⟩

    sampleTerm : Term SampleSymbol 1
    sampleTerm = (_ , Π) , ⟨ (_ , 𝓋) ∷ (_ , 𝓋) ∷ [] , (λ { zero → ⟨ 0 , (λ ()) ⟩ ; (suc zero) → ⟨ 1 , (λ ()) ⟩ ; (suc (suc ()))}) ⟩

    sampleWeaken : Term SampleSymbol 3
    sampleWeaken = wkTerm (wkTerm sampleTerm)

    data SampleReal (#fv : #FV) : Set where
      𝒰 : Universe → SampleReal #fv
      𝓋 : Fin #fv → SampleReal #fv
      Π : SampleReal #fv → SampleReal (suc #fv) → SampleReal #fv

    normalise' : ∀ {#fv : #FV} → (π : Σ Grammar SampleSymbol) → ITree (termC SampleSymbol) (π , #fv) → SampleReal #fv
    normalise' (universe , _) ⟨ ℓ , _ ⟩ = 𝒰 ℓ
    normalise' (variable , _) ⟨ v , _ ⟩ = 𝓋 v
    normalise' (term .(0 ∷ 1 ∷ []) , Π) ⟨ π₁ ∷ π₂ ∷ [] , r ⟩ = Π (normalise' π₁ (r zero)) ((normalise' π₂ (r (suc zero))))

    normalise : ∀ {#fv : #FV} → Term SampleSymbol #fv → SampleReal #fv
    normalise (g , y) = normalise' g y

    test : normalise sampleWeaken ≡ Π (𝓋 (suc (suc zero))) (𝓋 (suc (suc (suc zero))))
    test = refl

{-
  substitution

  given N is a number of free variables, substitute the variable v (from 0 to N - 1) in the right-hand term (which has N + 1 free variables) for the left-hand term (which has N free variables) resulting in a term having N free variables.
-}

  module _ {S : Symbol} where

    sbLetter : ∀ {#fv : #FV}
               → (σₗ : Letter S)
               → Fin (suc #fv)
               → (τₗ : Letter S) → ITree (termC S) (τₗ , (suc #fv))
               → Letter S
    sbLetter σₗ iₓ (universe , 𝓊) _ = _ , 𝓊
    sbLetter σₗ iₓ (variable , 𝓋) ⟨ iᵥ , _ ⟩ = ifYes iₓ == iᵥ then σₗ else (_ , 𝓋)
    sbLetter σₗ iₓ (term binders , s) τ = _ , s

    weakened-iₓ : ∀ {#fv} (binder : Nat) → Fin (suc #fv) → Fin (suc (binder + #fv))
    weakened-iₓ binder iₓ = transport Fin auto (wkFinByFrom binder zero iₓ)

    sbLetters : ∀ {#fv N} (σₗ : Σ Grammar S) →
                Fin (suc #fv) →
                (binders : Vec Nat N) (ls : Vec (Σ Grammar S) N) →
                ((p : Fin N) →
                 ITree (termC S) (indexVec ls p , indexVec binders p + suc #fv)) →
                Vec (Σ Grammar S) N
    sbLetters {#fv} σₗ iₓ binders ls r = tabulate λ p →
      let binder = indexVec binders p
          iₓ = weakened-iₓ binder iₓ
          l = indexVec ls p
          τ : ITree (termC S) (l , suc (indexVec binders p + #fv))
          τ = transport (ITree (termC S) ∘ (l ,_)) auto (r p)
      in
        sbLetter σₗ iₓ l τ

    {-# TERMINATING #-}
    sbITreeIx : ∀ {#fv} (σₗ : Σ Grammar S) (σ : ITree (termC S) (σₗ , #fv))
            (iₓ : Fin (suc #fv)) → ∀ {N}
            (binders : Vec Nat N) (ls : Vec (Σ Grammar S) N)
            (r
             : (p : Fin N) →
               ITree (termC S) (indexVec ls p , indexVec binders p + suc #fv))
            (p : Fin N)
          → ITree (termC S)
                  ( indexVec (sbLetters σₗ iₓ binders ls r) p
                  , indexVec binders p + #fv)
    sbITree : ∀ {#fv} (s : Σ Grammar S) →
              ITree (termC S) (s , #fv) →
              (iₓ : Fin (suc #fv)) (t : Σ Grammar S)
              (τ : ITree (termC S) (t , suc #fv)) →
              ITree (termC S) (sbLetter s iₓ t τ , #fv)

    sbITree 𝑠ₗ 𝑠 iₓ (universe , 𝓊) ⟨ ℓ , _ ⟩ = ⟨ ℓ , (λ ()) ⟩
    sbITree 𝑠ₗ 𝑠 iₓ (variable , 𝓋) ⟨ iᵥ , _ ⟩ with iₓ == iᵥ
    ... | yes refl = 𝑠
    ... | no iₓ≢iᵥ = ⟨ sbFin iₓ≢iᵥ , (λ ()) ⟩
    sbITree 𝑠ₗ 𝑠 iₓ (term binders , 𝓉) ⟨ ls , r ⟩ = ⟨ sbLetters 𝑠ₗ iₓ binders ls r , sbITreeIx 𝑠ₗ 𝑠 iₓ binders ls r ⟩

    sbITreeIx 𝑠ₗ 𝑠 iₓ [] ls r ()
    sbITreeIx {#fv} 𝑠ₗ 𝑠 iₓ (binder ∷ _) (l ∷ ls) r zero =
      let 𝑠 = wkITermByFrom binder zero 𝑠
          iₓ : Fin (suc (binder + #fv))
          iₓ = transport Fin auto (wkFinByFrom binder zero iₓ)
          τ : ITree (termC S) (l , suc (binder + #fv))
          τ = transport (ITree (termC S) ∘ (l ,_)) auto (r zero)
          -- l = sbLetter 𝑠ₗ iₓ l τ
      in
       sbITree 𝑠ₗ 𝑠 iₓ l τ
    sbITreeIx 𝑠ₗ 𝑠 iₓ (_ ∷ binders) (_ ∷ ls) r (suc p) = sbITreeIx 𝑠ₗ 𝑠 iₓ binders ls (r ∘ suc) p

    sbTerm : ∀ {#fv : #FV}
             → Term S #fv -- the substituted thing, 𝑠
             → Fin (suc #fv) -- which variable it replaces, x
             → Term S (suc #fv) -- the term in which to do the replacement, τ
             → Term S #fv -- the term after substitution, τ[𝑠/x]
    sbTerm (𝑠ₗ , 𝑠) iₓ (τₗ , τ) = sbLetter 𝑠ₗ iₓ τₗ τ , sbITree 𝑠ₗ 𝑠 iₓ τₗ τ
```

Substitution in Petersson-Synek trees is hard. Let's try with `Desc`. ... actually, that works no better. The trouble has to do with not being able to convince Agda's termination checker.
