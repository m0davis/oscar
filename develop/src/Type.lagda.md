
# Type theory, metaprogrammed (eventually)

```agda
module Type where
```

I develop a partial (or maybe a full) implementation of a particular type theory and then turn back to re-develop it as an instance of a general (metaprogrammed) type theory.

# Specification of Type Theory (from the HoTT book, mostly)

This is inspired mainly from Appendix A.2, though I have taken a liberty or two.

```agda
open import Type.Prelude
```

My first attempt at implementing a type theory was to represent that from the HoTT book, Appendix 2. I added a notion of complexity on the idea that it would help in proving that type inference (finding a term that witnesses a given type) is semi-decidable (that eventually, in some sense, any type capable of being witnessed will in fact be witnessed). I ran into trouble with cumbersome substitutions of DeBruijn-indexed variables. An idea to streamline the process was to use a mutually-defined weakening function for terms.

```
module SandboxMutual where
  open import Type.Theory.Mutual
  open import Type.Complexity
  open import Type.SCTerm
  open DefinedFunctions

  check-𝟙→𝟙 : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F ⋖ c (c [] ∷ c [] ∷ [])
  check-𝟙→𝟙 = ΠI zero 𝟙F (Vble refl)

  infer-𝟙→𝟙 : [] ⊢ ΠF 𝟙F 𝟙F
  infer-𝟙→𝟙 = ΠI (𝓋 zero) ,, c (c [] ∷ c [] ∷ []) ,, ΠI zero 𝟙F (Vble refl)

  check-𝟎=𝟎 : [] ⊢ =I 𝟎 ∶ (𝟎 =ℕ 𝟎)
  check-𝟎=𝟎 = c (c [] ∷ c [] ∷ []) ,, =I zero ℕF ℕIZ

  infer-𝟎+𝟎=𝟎 : [] ⊢ (𝟎 =ℕ 𝟎)
  infer-𝟎+𝟎=𝟎 = =I ℕIZ ,, c (c [] ∷ c [] ∷ []) ,, =I zero ℕF ℕIZ

  check-𝟎+𝟏=𝟏 : [] ⊢ =I 𝟏 ∶ ((𝟎 +ℕ 𝟏) =ℕ 𝟏)
  check-𝟎+𝟏=𝟏 = {!!} ,, {!!}

  infer-∀n→doublen=𝟐*n : [] ⊢ ΠF ℕF
                                 let n = 𝓋 zero in (double n =ℕ (𝟐 *ℕ n))
  infer-∀n→doublen=𝟐*n = ΠI (=I (𝓋 zero)) ,, {!!} ,, {!!}

  check-upsetting : [] ⊢ ℕIS 𝟙I ∶ ℕF
  check-upsetting = {!!} ,, {!!}
```

Then another idea was to come-up with a method for referring to variables by their names.

```agda
import Type.Theory.oldname -- this is some previous development of `Named`?
```

```
module SandboxNamed where
  open import Type.Theory.Named
  open import Type.SCTerm
  open DefinedFunctions

  check-𝟙→𝟙 : ε ⊢ ΠF 𝟙F 𝟙F ∋ ΠI (𝓋 zero)
  check-𝟙→𝟙 = {!!}

  infer-𝟙→𝟙 : ε ⊢ ΠF 𝟙F 𝟙F
  infer-𝟙→𝟙 = {!!}

  check-𝟎=𝟎 : ε ⊢ 𝟎 =ℕ 𝟎 ∋ =I 𝟎
  check-𝟎=𝟎 = {!!}

  infer-𝟎+𝟎=𝟎 : ε ⊢ (𝟎 =ℕ 𝟎)
  infer-𝟎+𝟎=𝟎 = {!!}

  check-𝟎+𝟏=𝟏 : ε ⊢ ((𝟎 +ℕ 𝟏) =ℕ 𝟏) ∋ =I 𝟏
  check-𝟎+𝟏=𝟏 = {!!}

  infer-∀n→doublen=𝟐*n : ε ⊢ ΠF ℕF
                                 let n = 𝓋 zero in (double n =ℕ (𝟐 *ℕ n))
  infer-∀n→doublen=𝟐*n = {!!}

  check-upsetting : ε ⊢ ℕF ∋ ℕIS 𝟙I
  check-upsetting = {!!}
```

While trying to define a type-checked notion of substitution of a variable defined in one context for a term in a different (but, somehow, compatible) context, I discovered that representing type membership in a linear context would require representing the dependency structure. This is unlike in STLC, where a type can be identified by its encoding. In a dependent type, the encoding of the same type may be different, depending on the postitions of the types depended upon in the context. This reminded me of the tree-like structure of an argument from several premises to a conclusion.

```agda
import Type.Argument
```

`Argument` was just getting started when I went back to `Named` with the idea I might have a fix. While working on that, I thought that it would be helpful to prove that one can apply term instantiation and weakening in different orders and produce equal results. However, when I tried to prove this, I found it quite cumbersome and was reminded of the McBride's advisement against "green slime" in "How to Keep Your Neighbours in Order". I realised then that I had a more fundamental problem.

McBride's advice is to shift the question of "what should the type of a subtree tell us?" to "what should we tell the type of the subtree?". I take it that the question of "what *does* the type of a subtree tell us?" is answered by its indices. I further take it that the question of "what *do* we tell the type of a subtree?" is answered by its constructors.

Before the shift, the indices of a subtree includes a 2-bit telling us whether the subtree is a leaf or not, and if it is not a leaf, two values (inhabitants of (P : Set), a parameter giving the type of things ordered by the subtrees) telling us the greatest and least elements of its own left and right subtrees, respectively. After the shift, the indices of a subtree includes two 3-bits, and for each, depending on whether the 3-bit carries the second of its three particulars, a value (inhabitant of P).

For now, this is as far as far as I will go in deciphering McBride's wisdom: I see that it may be important to encode as much information in the indices of a type as may be available. Not having a formal education in information theory, this may be a little rough: I compute that before the shift, the indices yield the following number of bits: 2 + max (0 , ω²) = 2 + ω². After the shift, we have (3 + max (0 , ω , 0))² = 9 + 6ω + ω², which is strictly greater than the former.

In `Named`, the type-inhabitation type,

    data _⊢_∋_ {N} (Γ : N ctx) : STerm N → STerm N → Set

does *not* tell us that the inhabited type is a type! (It is somewhat confusing to use "type" in two different senses: one, as an Agda type (inhabitant of Set), another as a type that I am trying to encode theoretically. Less confusingly, Γ ⊢ A ∋ a does not tell us that Γ ⊢ A ∈ ℓ.) I believe the consequence of redefining type-inhabitation to

    data _⊢_∋_ {N} (Γ : N ctx) : ⊣ Γ → STerm N → Set

will be that the green slime of weakening and substitution be relegated to the universe-inhabitation type, `_⊢_∈_`.

Perhaps something can be done about the definitional-equality type?

    data _⊢_≝_∶_ {N} (Γ : N ctx) : STerm N → STerm N → STerm N → Set

Shifting around the indices, I imagine something like this:

    data _⊢_∋_≝_ {N} (Γ : N ctx) : ∀ {ℓ} (τ : Γ ⊢ A ∈ ℓ) → Γ ⊢ τ → Γ ⊢ τ → Set

Lest I go too far, what about the type constructor for universe-inhabitation from type-inhabitation?

    ⟨_⟩ : ∀ {N} {Γ : N ctx}
        → ∀ {𝑨 ℓ}
        → Γ ⊢ 𝒰 ℓ ∋ 𝑨
        → Γ ⊢ 𝑨 ∈ ℓ

We would then construct such an inference as

    ⟨_⟩ : ∀ {N} {Γ : N ctx}
        → ∀ {𝑨 ℓ} {τ : Γ ⊢ 𝒰 ℓ ∈ ℓ}
        → Γ ⊢ τ ∋ 𝑨
        → Γ ⊢ 𝑨 ∈ ℓ

I guess that is not a problem. I'm unclear why I thought it would be: it was some concern over mutually-defined datatypes, but I don't see the issue at the moment.

More concerning is the remaining green slime. As anticipated, I will have it in the universe-inhabitation's `suppose`, which invokes `weakenTermFrom` and, as I guess I will call it, `apply`, which will invoke `applyTerm`. In addition, there is the `variable` constructor for type-inhabitation. Given the shift towards making type-inhabitation supply us a universe-inhabitant, how might I redefine `variable`? It was:

    variable : (x : Fin N)
             → Γ ⊢ (Γ at x) .sterm ∋ 𝓋 x

Upon redefinition, it becomes

    variable : (x : Fin N)
             → Γ ⊢ (Γ at x) ∋ 𝓋 x

which still has green slime, but least is relegated to a single constructor.

I try this out in:

```agda
import Type.Theory.Slimdex
```

I also had another idea, thinking maybe I could just build much more information into the indices of the type. I tested it out here:

```agda
import Type.Slimeless
```

Yet another idea is to represent renaming and substitution with datatypes. How to do this?

Idea #1

For renaming, we would have:

    Γ ⊢ A ∋ x ⊆ Δ ⊢ B ∋ y

meaning that the right-hand judgement may be obtained from the left-hand judgement via a procedure of weakening and variable swapping.

For substitution, we would have

    ??

Idea #2

Wrap weakening and instantiation in datatypes that provide some type-checking on the constituents. We would

sideline weakening and instantiation into another datatype whose constructors represent those actions. The datatype's indices would express that two terms in different contexts are equivalent

Idea #3

Same as #2 but there's no need for sidelining it into a datatype. We just create a type constructor (a function into Set) whose inputs are checked to give us the sort of sanity-guarantees we want and whose output is an equation involving weakenTermFrom and/or instantiateTerm.

Subproperty relation: Γ is a subproperty of Δ, written Γ ≽ Δ

_≽_ : ∀ {N} (Γ : N ctx) → ∀ {M} → M + N ctx → Set
Γ ≽ Δ = ∀ {τ} → Γ ⊢ τ → Δ ⊢ τ

or maybe instead, we have a Debruijn-index for context membership

data _∈_ {N} {Γ : N ctx} {𝑨 : STerm N} (τ : 𝑨 ⊣ Γ) : ∀ {M} → M ctx → Set where
  zero : τ ∈ Γ , τ
  suc : ∀ {M} {Δ : M ctx} {𝑮}
         → {γ : 𝑮 ⊣ Δ}
         → τ ∈ Δ
         → τ ∈ Δ , γ

weakenedCtx[_]≈_at[_]with[_] :
  ∀ {N}
  → (Γ : N ctx)
  → (Δ : suc N ctx)
  → (at : Fin (suc N))
  → (w : Γ₀ ⊢ δ ∈ ℓ)
  → Set

weakenedTerm[_]≈_from[_] : ∀ {N} {Γ : N ctx}
                           {𝒙 : STerm N}
                           {𝒙' : STerm (suc N)}
                           (A : Γ ⊢ 𝑨 ∈ ℓ)
                           (A' : Δ ⊢ 𝑨' ∈ ℓ)
                         → (τ : Γ ⊢ 𝑨 ∋ 𝒙)
                         → (τ' : Δ ⊢ 𝑨' ∋ 𝒙')
                         → (from : A' ∈ Γ)
                         → Set
weakenedTerm[_]≈_from[ zero ] =
  Γ weakenTermFrom from 𝑨
weakened[_]≈_at[_]
  {𝒙 = 𝒙} τ
weakened[ τ ]≈ τ' at[ from ] = weakenTermFrom from 𝒙 ≡ 𝒙'
  ∀ {N} {Γ : N ctx}
  → (τ : Γ ⊢ A ∋ x)
  → (τ' :
  → Set
  where
  wk :
     →
     →
     →

Idea #4

Waay back at `Type.First`, I had something like this (plus some complexity stuff)

    ΣF : ∀ {ℓ 𝑨 𝑩}
       → (A : Γ ⊢ 𝑨 ∶ 𝒰 ℓ)
       → Γ , A ⊢ 𝑩 ∶ 𝒰 ℓ
       → Γ ⊢ ΣF 𝑨 𝑩 ∶ 𝒰 ℓ
    ΣI : ∀ ℓ {𝑨 𝑩 𝒂 𝒃}
       → (A : Γ ⊢ 𝑨 ∶ 𝒰 ℓ)
       → Γ , A ⊢ 𝑩 ∶ 𝒰 ℓ
       → Γ ⊢ 𝒂 ∶ 𝑨
       → Γ ⊢ 𝒃 ∶ instantiateTerm zero 𝒂 𝑩
       → Γ ⊢ ΣI 𝒂 𝒃 ∶ ΣF 𝑨 𝑩
    ΣE : ∀ ℓ 𝑨 𝑩 {𝑪[𝒑] 𝑪 𝒈 𝒑}
       → (A : Γ ⊢ 𝑨 ∶ 𝒰 ℓ)
       → (B : Γ , A ⊢ 𝑩 ∶ 𝒰 ℓ)
       → Γ , ΣF A B ⊢ 𝑪 ∶ 𝒰 ℓ
       → Γ , A , B ⊢ 𝒈 ∶ instantiateTerm (suc (suc zero))
                                         (ΣI (𝓋 (suc zero)) (𝓋 zero))
                                         (weakenTermFrom zero (weakenTermFrom zero 𝑪))
       → Γ ⊢ 𝒑 ∶ ΣF 𝑨 𝑩
       → 𝑪[𝒑] ≡ instantiateTerm zero 𝒑 𝑪
       → Γ ⊢ ΣE 𝑪 𝒈 𝒑 ∶ 𝑪[𝒑]

Now, I'd like to build-up the defining argument for `g` like so:

    ΣE : ∀ ℓ 𝑨 𝑩 {𝑪[𝒑] 𝑪 𝒈 𝒑}
       → (A : Γ ⊢ 𝑨 ∶ 𝒰 ℓ)
       → (B : Γ , A ⊢ 𝑩 ∶ 𝒰 ℓ)
       → (C : Γ , ΣF A B ⊢ 𝑪 ∶ 𝒰 ℓ)
       -- C's context weakened from (suc zero) with A giving a then weakened from (suc zero) with B giving b then substituting the suc (suc zero) element with ΣI a b
       → (let C,A : Γ , ΣF A B , ???
          let G : Σ (Term _) λ 𝑪' → Γ , A , B ⊢ 𝑪' ∶ 𝒰 ℓ
              G = Subst₁ (Wkg₁ B (Wkg₁ A C))

       -- → g ≈ apply (wk ⊢B (wk ⊢A ⊢C)) (lamda ⊢A λ a → lambda ⊢B λ b → ΣI a b)
       →
       → Γ ⊢ 𝒑 ∶ ΣF 𝑨 𝑩
       → 𝑪[𝒑] ≡ instantiateTerm zero 𝒑 𝑪
       → Γ ⊢ ΣE 𝑪 𝒈 𝒑 ∶ 𝑪[𝒑]

Idea #5

Carry out what I had barely started in `Type.Mutual` and implement proofs of Subst₁ and Wkg₁ (and also their definitional-equality counterparts). But the trick will be in even stating the theorems because the context, as I have so far defined it, is itself a proof that the context consists of (type-checked) universe inhabitants. Perhaps an easier way to go will be to take the context over which the typing judgement applies to be a (snoc?) list of `Term _`, then have a separate judgement that validates the context for those rules (such as 𝒰-intro) that call for such a thing. This will more closely represent what's formalised in Appendix A.2 of the HoTT book.

```agda
import Type.HoTTer
```

There, finding that I needed to build-up from syntactically-valid forms to well-scoped expressions (and not the other way around), I proceed to:

```agda
import Type.Theory.Building
```

The proof for the (admissable) weakening rule for well-typed terms confused me. I suspect I could clarify the situation if I removed the green slime. The lazy way to do this is simply to put the green stuff in outputs in argument positions using propositional equality. Which is what I try here:

```agda
import Type.Theory.Guilding
```

All was going well it seemed until Agda gave me the sugar-me-do, allowing me to fill a hole but then complaining about it afterwards. As this is not type-theory related, I sideline the investigation into how this can happen separately.

```agda
import Agdasugarmedo
```

It turns out that the problem experienced about is caused by absurd lambdas inheriting the parameters of the datatype in which they are mutually defined with a function that uses that lambda. The solution is to move the computation of the absurd lambda outside the datatype.

```
module SandboxOuting where
  open import Type.Theory.Outing
  open import Type.Theory.Outing.Admissible
  open import Type.Context
  open import Type.Formula
  open DefinedFunctions

  check-𝟙→𝟙 : ε ⊢ ΠI 𝟙F (zero ↦₁ 𝓋 zero) ∶ ΠF 𝟙F (zero ↦₁ 𝟙F)
  check-𝟙→𝟙 = ΠI (var (ctx-EXT {ℓ = zero} (𝟙F ctx-EMP) unit) zero refl)

  infer-𝟙→𝟙 : ε ⊨ ΠF 𝟙F (zero ↦₁ 𝟙F)
  infer-𝟙→𝟙 = ⟨ ΠI 𝟙F (zero ↦₁ 𝓋 zero) ∶ ΠI (var (ctx-EXT {ℓ = zero} (𝟙F ctx-EMP) unit) zero refl) ⟩

  check-𝟎=𝟎 : ε ⊢ =I 𝟎 ∶ 𝟎 =ℕ 𝟎
  check-𝟎=𝟎 = =I (ℕIᶻ ctx-EMP)

  infer-𝟎+𝟎=𝟎 : ε ⊨ 𝟎 +ℕ 𝟎 =ℕ 𝟎
  infer-𝟎+𝟎=𝟎 = ⟨ {!!} ∶ {!!} ⟩

  infer-∀n→doublen=𝟐*n : ε ⊨ ΠF ℕF
                                (let n = 0 in
                                  n ↦₁ double (𝓋 n) =ℕ 𝟐 *ℕ (𝓋 n))
  infer-∀n→doublen=𝟐*n = {!!}

  check-not-upsetting : ε ⊢ ℕIˢ 𝟙I ∶ ℕF → ⊥
  check-not-upsetting = {!!}
```
