
# Wherein I have realised something about datatypes. ...or have I?

```agda
module YAF10 where
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

  add-zero : ∀ n → n ≡ n +N 0
  add-zero zero = refl
  add-zero (suc n) = cong suc (add-zero n)
```

It's very unclear to me still what we use parameters for and what for indexes. The best I have is that the parameter is "carried" (whatever that means) by the type. I have Vec (A : Set) : ℕ → Set as my prototypical example. `A` doesn't change for each constructor but `ℕ` does vary. If we were building a heterogeneous Vec then I guess `A` would become an index. Is that even possible?

```agda
module HetVecExperiment where

  open Preliminary

  data HetVec : Set → Nat → Set₁ where
    [] : HetVec ⊥ zero
    _∷_ : {A : Set} → A → {B : Set} {n : Nat} → HetVec B n → HetVec A (suc n)

  test-0 : HetVec ⊥ zero
  test-0 = []

  test-2 : HetVec Nat 2
  test-2 = 3 ∷ ("String" ofType String) ∷ []
```

Well by golly, it works.

So, perhaps I can now explain why I need to have the context be part of the index and not the parameter to the datatype `Term` which is intended to represent all inhabited types (given any particular set of suppositions). I had trouble when it came to trying to say that for a given context, any type that resided in that context could be considered inhabited. If the datatype `Type` represented all ways in which a type could inhabit a universe (given any particular set of suppositions) then I might have been able to construct a type at the top-level of my given context from one of the suppositions within the context. That is, I would have been able to prove the following lemma:

  extendHead : {N : Nat} (Γ : Context N) {ℓ : Nat} (σ : Type Γ ℓ) → Type (Γ ,, σ) ℓ

or something like that. I guess the point is that, while it might have been possible to do (as we have seen by defining Fin`e` with a Σ, it would have been difficult.

That's not a very satisfying explanation, so there could be trouble ahead. Nevertheless, going forth...

I will take the context as part of the index of the `Type` datatype (which is supposed to show all ways a universe (of a given level) might be inhabited (by a type)... Boy do I need to understand what the he-double-hockey-sticks this actually means: what's a "universe"? ---of discourse? ---a set of assertions or propositions? What's the deal with the levels? ----------

Now, what about building up the `Term` datatype? If we already are able to say that some type lies in a subcontext of a given context Γ, and we are able to lift this type up out of the subcontext to the given one, then maybe we don't need an index. However, it seems this might still be difficult.

Something that bothers me: I seem to need a rule (constructor) for weakening `Type`s and also a rule for weakening `Term`s. But Appendix A.2 shows these as the same judgemental form. Related to this is the fact that I seem to have no way of saying that U₀ is a "proof" of U₁, because that would mean that I could say `Term [] (𝒰-intro 1)`. But there is no such constructor for `Term`s. The obvious one would be 𝒰-intro : (ℓ : Nat) → Term Γ (𝒰-intro (suc ℓ)). But this seems needlessly repetitive. Can I even say that ℕ is a proof of U₀? Again, no. I would need something like `type-intro : {ℓ : Nat} → (σ : Type Γ ℓ) → Term Γ σ`. Okay, so that's not so bad.

Nevertheless, is it a good idea to combine `Type` and `Term`? How would we then define contexts? We would need to think of judgements in the form `list-of-terms-that-inhabit-universes ⊢ generic-term : term-that-inhabits-a-universe`. This would get somewhat complicated, so it seems good to keep them separate.

Before I proceed, let's go a little deeper. We will also eventually need computation rules. That seems to require yet another datatype, but then we will want to link that to the `Term` datatype so that any judgemental equalities can be used to build-up type-inhabitation judgements.

This will make the number of ways of inhabiting a type quite extraordinary. But let me remind myself that it's okay, so long as I can prove that the empty type is not inhabited. There may be no way to define (σ : Type [] zero) → Dec (Term [] σ). (I'm still not sure whether there is or not, but I suspect not.) So what's the point? If I conjecture that a particular type is inhabited (and given that I'm correct), I want a procedure that proves inhabitation. So what function is wanted? It seems silly to define:

(σ : Type [] zero) → Term [] σ → Term [] σ

So what is wanted is something like:

(σ : Type [] zero) → Inhabited (Term [] σ) → Term [] σ

where `Inhabited : Set → Set` gives a witness that the term is inhabited without giving any clue as to how it might be so. Yet such a thing may be impossible to define for the same reason that we cannot (maybe) decide inhabitation.

Let's see if such a thing is even possible to do in Agda.

```agda
module ErasedInhabitation where

  open Preliminary

  Inhabited : Set → Set
  Inhabited x = ¬ ¬ x

  checkIt : Inhabited Nat → Nat
  checkIt x = {!!} -- yup, that certainly gives us no clue. There's the "pure gain" that Robert Harper was talking about

  checkIt-⊥ : Inhabited ⊥ → ⊥
  checkIt-⊥ x = x λ () -- and that works as expected.
```

It still is somewhat mysterious to me whether or not type inhabitation is decidable. Well, the way people talk about it, it looks like it's not. But I'm not clear on why. And it still seems like certain problems (such as GCD) should be reducible to a decidable thingy.

Considering further the induction principle for natural numbers, it's more clear that type inhabitation might not be decidable. Unlike the other induction principles, backwards reasoning from ℕ-elim leads to a *more* complicated (larger) interest, albeit with a possibly-helpful suppostion. With each of the the other elimination rules, we reduce the total number of type formers in the interest. (that last part might not be quite correct, but it's close).

Now, the same thing can be said for FOL. Derivability (like type inhabitation) is not decidable. On the bright side, there is a procedure that will find a derivation for any sentence given that the sentence is true (true in all models, true in all interpretations). There is a "semantics" for FOL that gives us that P is derivable iff P is true. I wonder what the use of such semantics is. Given a finite set of rules for making derivations, it is obvious that there is a procedure that will find a derivation iff the sentence is derivable from the rules: we simply attempt to apply each of the rules in parallel, producing longer and longer derivations, until we achieve a derivation of the sentence. If such a procedure does not find a derivation of the sentence, then there is no (finite length) derivation. Anyway, that is beyond obvious.

My idea was to create a programming language in which I would not have to give proofs for certain derivable propositions I might declare. Then I would simply say "there is a GCD", and the system would try to construct a program for obtaining a GCD. If I am unfortunate enough to declare something for which there is no derivation (program), then I might be waiting a long time (forever) for the system to eventually come back to tell me that it cannot do so. But, that's okay, I thought: most of the time, I will write things that I know are provable, and I want to move on with writing those things, not spend time working on problems I know can be solved mechanically.

Given the way I imagine doing a proof search with the type theory from Appendix A.2, what would happen if I asked for a search of Π (A : 𝒰₀) (A + Π (x : A) 0)?? Or for a search of 0? In the latter case, we will immediately exahaust the search space, for there are no applicable rules (the way I'm thinking about doing it). In the former case, we may proceed as follows (backwards reasoning):

() ⊢ ??1 : Π (A : 𝒰₀) (A + Π (x : A) 0)
() ⊢ λ (A : 𝒰₀) . ??2 : Π (A : 𝒰₀) (A + Π (x : A) 0)
(A : 𝒰₀) ⊢ ??2 : (A + Π (x : A) 0)

(A : 𝒰₀) ⊢ inl ??3.1 : (A + Π (x : A) 0)
(A : 𝒰₀) ⊢ ??3.1 : A -- here we stop b/c we don't have a rule that introduces A ... but what we had a context of (A : 𝒰₀ , f : 1 → A)?

(A : 𝒰₀) ⊢ inr ??3.2 : (A + Π (x : A) 0)
(A : 𝒰₀) ⊢ ??3.2 : Π (x : A) 0
(A : 𝒰₀) ⊢ λ (x : A) . ??4.2 : Π (x : A) 0
(A : 𝒰₀) (x : A) ⊢ ??4.2 : 0 -- here we stop b/c we don't have a rule that introduces 0 -- but see question above

Let's try the following

() ⊢ ??1 : Π (A : 𝒰₀) (Π (f : Π (x : 1) A) (A + Π (x : A) 0))
() ⊢ λ (A : 𝒰₀) . ??2 : Π (A : 𝒰₀) (Π (f : Π (x : 1) A) (A + Π (x : A) 0))
(A : 𝒰₀) ⊢ ??2 : Π (f : Π (x : 1) A) (A + Π (x : A) 0)
(A : 𝒰₀) ⊢ λ (f : Π (x : 1) A) . ??3 : Π (f : Π (x : 1) A) (A + Π (x : A) 0)
(A : 𝒰₀) (f : Π (x : 1) A) ⊢ ??3 : A + Π (x : A) 0

(A : 𝒰₀) (f : Π (x : 1) A) ⊢ inl ??4.1 : A + Π (x : A) 0
(A : 𝒰₀) (f : Π (x : 1) A) ⊢ ??4.1 : A -- here we want to use Π-elim

We easily have Γ ⊢ f : Π (x : 1) A for one of the premises of Π-elim. Now we try to match the dependent clause of the Π-term with our interest.

It's not clear to me that this will always work. We may be wanting to use Π-elim on all things that we could reason forwards from. But then the trouble is if we have Π (x : ℕ) B. We want to match our interest with B (which has a placeholder for the independent clause) and then develop interests in each possible instantiator for the independent clause. But this could get very explosive combinatorically. For example, say we have an interest in x + 0 = x, and we have that Π (w : ℕ) (w + 0 = w).

(A : 𝒰₀) (f : Π (x : 1) A) ⊢ inr ??4.2 : A + Π (x : A) 0
(A : 𝒰₀) (f : Π (x : 1) A) ⊢ ??4.2 : Π (x : A) 0
(A : 𝒰₀) (f : Π (x : 1) A) ⊢ λ (x : A) . ??5.2 : Π (x : A) 0
(A : 𝒰₀) (f : Π (x : 1) A) (x : A) ⊢ 0 -- stopping b/c ?


Here's what is troubling me. How do we prove this

```agda
module VeryEasyButTroubling where
  open Preliminary
  easyTTA : ∀ (A : Set) → (⊤ → ⊤ → A) → A
  easyTTA = λ _ f → f tt tt
```

After introducing Π terms we get the following interest

A : 𝒰₀ , f : Π (x : 1) (Π (y : 1) A) ⊢ ?? : A

Let Γ₁ = A : 𝒰₀ , f : Π (x : 1) (Π (y : 1) A). We can reason forwards to the following

Γ₁ ⊢ A : 𝒰₀
Γ₁ ⊢ f : Π (x : 1) (Π (y : 1) A)

Given we already have

Γ₁ ⊢ ⋆ : 1

we can use Π-elim twice to conclude

Γ₁ ⊢ f ⋆ : (Π (y : 1) A)
Γ₁ ⊢ f ⋆ ⋆ : A

But it we had ℕ instead of 1, there would have been several more possibilities! For example, try this slightly harder problem:

```agda
module SlightlyHarderTrouble where
  open Preliminary
  harder : (A : Nat → Nat → Set) (f : (m n : Nat) → A m n) → A 5 3
  harder A f = f 5 3

  harder' : (A : Nat → Nat → Set) (f : (m n : Nat) → A m n) → (m : Nat) → A m 3
  harder' A f m = f m 3
```

How could we use Π-elim in a backwards way? By reasoning forwards from

(f : (m n : Nat) → A m n)

Let's try the following backwards-forwards rule:

Γ ⊢ f : Π (x : A) B
---------------------------
Γ , a : A ⊢ f a : B[a / x]

This says that if we have f : Π (x : A) B, we can reason forwards to a situation where, if we ...

Okay, given interest in A 5 3, by Π-elim, we look for any of the following:

Π (x : ?1) ...

No, this reminds me of the "parallelising" part of John's parallelising reductio.

We should maybe reason forwards using Π-elim when the number of possible forwards conclusions is finite. Otoh, when we have a Π depending on an ℕ, then we reason forwards in a schematic way....

Γ ⊢ f : (m n : Nat) → A m n
Γ , m : Nat ⊢ f m : (n : Nat) → A m n
Γ , m : Nat , n : Nat ⊢ f m n : A m n

Now we are interested in

Γ ⊢ ?? : A 5 3

Noting that the last of these matches, with m ≡ 5 and n ≡ 3, we become interested in

Γ ⊢ m ≡ 5 : Nat
Γ ⊢ n ≡ 3 : Nat

I guess it's time to revisit Natural Deduction.

The idea is that if we are interested in Γ ⊢ P, and we have Γ,Δ ⊢ Q, where P matches Q except for variables in Δ, then we generate interest in Γ ⊢ Δ. Or something like that.


Here's a rendition of reasoning about `harder`:

I01.
  ()
  ⊢ ??I01 ≡ λ (A : Π (m : ℕ) (Π (n : ℕ) U₀)) . ??I02
  : Π (A : Π (m : ℕ)
             (Π (n : ℕ) U₀))
      (Π (f : Π (m : ℕ)
                (Π (n : ℕ) (A m n)))
         ((A (succ (succ (succ (succ (succ zero))))))
           (succ (succ (succ zero)))))

I02.
  (A : Π (m : ℕ) (Π (n : ℕ) U₀))
  ⊢ ??I02 ≡ λ (f : Π (m : ℕ) (Π (n : ℕ) (A m n))) . ??I03
  : Π (f : Π (m : ℕ)
             (Π (n : ℕ) (A m n)))
      ((A (succ (succ (succ (succ (succ zero))))))
        (succ (succ (succ zero))))

I03.
  (A : Π (m : ℕ) (Π (n : ℕ) U₀))
  (f : Π (m : ℕ)
         (Π (n : ℕ) (A m n)))
  ⊢ ??I03
  : (A (succ (succ (succ (succ (succ zero))))))
      (succ (succ (succ zero)))

C01.
  (A : Π (m : ℕ) (Π (n : ℕ) U₀))
  (f : Π (m : ℕ)
         (Π (n : ℕ) (A m n)))
  ⊢ f
  : Π (m : ℕ)
      (Π (n : ℕ) (A m n))

C02.
  (A : Π (m : ℕ) (Π (n : ℕ) U₀))
  (f : Π (m : ℕ)
         (Π (n : ℕ) (A m n)))
  (m : ℕ)
  ⊢ f m
  : Π (n : ℕ) (A m n)

C03.
  (A : Π (m : ℕ) (Π (n : ℕ) U₀))
  (f : Π (m : ℕ)
         (Π (n : ℕ) (A m n)))
  (m : ℕ)
  (n : ℕ)
  ⊢ f m n
  : A m n

So this seems easy enough. We simply unify I03 with C03 to see that we need m ≡ 5 : ℕ and n ≡ 3 : ℕ, which we can obtain via backwards reasoning using the ℕ-intro rules.

Let's make it a little harder. What if we change n : ℕ into something that depends on m?

Or is there a problem already? What if C03 contained an additional premise? Well, I guess that's the breaks, babe.

So, I'm thinking we have an interest like this:

I.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢ ??I03
  : (A (succ (succ (succ (succ (succ zero))))))
      (g (succ (succ (succ zero))))

and some conclusions like this:

C1.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (m : ℕ)
  ⊢ g m
  : B m

C2.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  (m : ℕ)
  (n : B m)
  ⊢ f m n
  : A m n

C2 unifies with I, generating interests based on the additional premises in C2 that are not in I.

C2/I.1.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢ (succ (succ (succ (succ (succ zero)))))
  : ℕ

C2/I.2.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢ g (succ (succ (succ zero)))
  : B (succ (succ (succ (succ (succ zero)))))

C2/I.1 is solved by backwards reasoning from ℕ-intro. C2/I.2 unifies with C1 to generate the interest

C1/I.2/C1
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢

--- umm, actually it doesn't unify. There's a mistake in my coding!

Let's verify that this really was never going to work

```agda
module MyMistake where
  open Preliminary
  postulate
    harderest :
      (B : Nat → Set)
      (g : (m : Nat) → B m)
      (A : (m : Nat) → B m → Set)
      (f : (m : Nat) (n : B m) → A m n)
      → A 5 {!(g 3)!} -- yup, the type doesn't even type-check.
```

Yup. Revising a bit, we would have:

I.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢ ??I
  : (A 5 (g 5))

C1.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (m : ℕ)
  ⊢ g m
  : B m

C2.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  (m : ℕ)
  (n : B m)
  ⊢ f m n
  : A m n

C2 unifies with I, generating interests based on the additional premises in C2 that are not in I.

C2/I.1.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢ 5
  : ℕ

C2/I.2.
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢ g 5
  : B 5

C2/I.1 is solved by backwards reasoning from ℕ-intro. C2/I.2 unifies with C1 to generate the interest

C1/I.2/C1
  (B : Π (m : ℕ) U₀)
  (g : Π (m : ℕ) (B m))
  (A : Π (m : ℕ) (Π (n : B m) U₀))
  (f : Π (m : ℕ)
         (Π (n : B m) (A m n)))
  ⊢ 5
  : ℕ



Alright. Now that I'm convinced that a natural deduction approach to an intuitionistic logic, I will proceed with constructing the type theory.

I need to clear-up this business about simultaneous substitution. There is the idea of "writing the free variables apart", which is I think exemplified by an example I've mentioned:

Bxy[y,x/x,y] = Bxy[x'/x][y'/y][y/x'][x/y']

For the moment, let's presume that x and y are the only free variables. We have something like this:

x : A , y : A ⊢ B : U
x : A , y : A , x' : A ⊢ B : U
x : A , y : A , x' : A ⊢ B[x'/x] : U
x : A , y : A , x' : A , y' : A ⊢ B[x'/x] : U
x : A , y : A , x' : A , y' : A ⊢ B[x'/x][y'/y] : U
x : A , y : A , y' : A ⊢ B[x'/x][y'/y]⟦y/x'⟧ : U
x : A , y : A ⊢ B[x'/x][y'/y]⟦y/x'⟧⟦x/y'⟧ : U

where ⟦_/_⟧ represents a kind of application, in which the context is strengthened. We could even represent [_/_] as a weakening action ... but let's not for now. We may need it to do things like [succ x/x].

Now the worry is that ⟦_/_⟧ may not work right if the substituted term or type is depended-upon by later types. In Subst we see that the solution for that is to also do the replacement on types later in the context. I am seeing now that substitution is something that modifies or applies to terms and types, and not so much that it forms them. I had an idea that I might ...

To build a function that does substitution of even one variable means that we need some way of referring to such things in the datatype.

Let's think of simultaneous substitution as a composition: sub(B,a,x,σ), where σ denotes further substitutions. sub(B,a,x,()) = B[x'/x]⟦a/x'⟧, sub(B,a,x,σ) = σ(B[x'/x])⟦a/x'⟧.

 Γ , x : A ⊢ B : U    Γ ⊢ a : A
---------------------------------
      Γ ⊢ B[a/x] : U

 Γ , x : A ⊢ b : B    Γ ⊢ a : A
--------------------------------- Π-Comp (or anyway, the rhs of it)
      Γ ⊢ b[a/x] : B[a/x]

 Γ , x : A ⊢ B : U    Γ , x : A ⊢ b : B    Γ ⊢ a : A
------------------------------------------------------
      Γ ⊢ B[a/x] : U       Γ ⊢ b[a/x] : B[a/x]


So I just now realised that we need only a variable in the Term datatype in order to make substitution doable. For example,

  () ⊢ Π (A : U₀) A : U₁

is represented as a Type [] 1 ≡ Π-form (𝒰-form 0) (variable 0)

which expresses the derivation

1
------ ctx-emp, 1
2 () ctx
------------- 𝒰-intro, 2
3 () ⊢ 𝒰₀ : 𝒰₁
------------- ctx-ext, 3
4 (x₁ : 𝒰₀) ctx
-------------- Vble, 4
5 (x₁ : 𝒰₀) ⊢ x₁ : 𝒰₀
----------------------- Π-form, 3, 5
6 () ⊢ Π (x₁ : 𝒰₀) x₁ : 𝒰₁

Ah, so Vble has indeed been the Term constructor I had been needing. But what's still a bit weird is that I am separating Term from Type. This is making the interpretation of line 5 somewhat awkweird.

What's kept me from simply declaring a typing judgement such as in Appendix A.2? I've wanted to keep a distinct notion of a /proposition/, which I called `Type`. Propositions were to live in the right-most-hand side of the typing judgement (judging a term to be of a certain type). But this stuff about the universes sorta screws with that idea. If I am to keep this `Type`/`Term` distinction, then I will at least need a separate Vble rule for each such kind of judgement.

So, let's skip this first try and try something even more sticking-to-the-book.

>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
>> ` ``agda
>> module TypeTheory-Try#1 where
>>
>>   open Preliminary
>>
>>   data Context : Nat → Set
>> {-
>>   data Form : {N : Nat} (Γ : Context N) → Nat → Set
>>
>>   data Intro : {N : Nat} → Context N -- the context of the term -- think of this as the assumptions used to prove the proposition being stated
>>             →
>>               {N : Nat} {Γ : Context N} {ℓ : Nat} → Type Γ ℓ -- the type of the term (in the context in which the type was formed) -- think of this as the information needed to describe the proposition being stated
>>             → Set
>> -}
>>   data Type : {N : Nat} (Γ : Context N) → Nat → Set
>>
>>   data Intro : {N : Nat} → Context N -- the context of the term -- think of this as the assumptions used to prove the proposition being stated
>>             →
>>               {N : Nat} {Γ : Context N} {ℓ : Nat} → Type Γ ℓ -- the type of the term (in the context in which the type was formed) -- think of this as the information needed to describe the proposition being stated
>>             → Set
>>
>>
>>   data Term : {N : Nat} → Context N -- the context of the term -- think of this as the assumptions used to prove the proposition being stated
>>             →
>>               {N : Nat} {Γ : Context N} {ℓ : Nat} → Type Γ ℓ -- the type of the term (in the context in which the type was formed) -- think of this as the information needed to describe the proposition being stated
>>             → Set
>>
>>   data Equation : {N : Nat} → (Γ : Context N)
>>                 →
>>                   {N : Nat} {Γ' : Context N} {ℓ : Nat} {T : Type Γ' ℓ}
>>                 → Term Γ T → Term Γ T → Set
>>
>>   data Derivation :
>>              {N : Nat} → (Γ : Context N)
>>            → {N : Nat} {Γ' : Context N} {ℓ : Nat} {T : Type Γ' ℓ}
>>            → Term Γ T → Set
>>
>>   -- substituteTerm :
>>
>>   infixl 5 _,,_
>>   data Context where
>>     [] : Context zero
>>     _,,_ : {N : Nat} (Γ : Context N) {ℓ : Nat} → Type Γ ℓ → Context (suc N)
>>
>>   -- indexContext : ∀ {N} (Γ : Context N) → Fin N → ∃ λ N'
>>
>>   data Type where
>>     𝒰-form : (ℓ : Nat) → Type [] (suc ℓ)
>>     Π-form : {N : Nat} {Γ : Context N} {ℓ : Nat} (π : Type Γ ℓ) → Type (Γ ,, π) ℓ  → Type Γ ℓ
>>     Σ-form : {N : Nat} {Γ : Context N} {ℓ : Nat} (σ : Type Γ ℓ) → Type (Γ ,, π) ℓ  → Type Γ ℓ
>>     ℕ-form : Type [] zero
>>     =-form : {Nt : Nat} {Γt : Context Nt} {NT : Nat} {ΓT : Context NT} {ℓT : Nat} {t : Type ΓT ℓT} → Term Γt t → Term Γt t → Type Γt ℓT -- unclear what to use for the context in the formed Type
>>     -- substitution : {N : Nat} {Γ : Context N} {ℓ : Nat} (π : Type Γ ℓ) (B : Type (Γ ,, π) ℓ)
>>     --              → Type Γ
>>
>>   data Term where
>>
>>   data Derivation where
>>
>>
>>
>>   data NFType where
>>
>>
>> {-
>>     𝒰-cumul : {N : Nat} {Γ : Context N} {ℓ : Nat} → Type Γ ℓ → Type Γ (suc ℓ)
>>     Γ-cumul : ∀ {N} {Γ : Context N} {ℓ ℓ'} (σ : Type Γ ℓ') → Type Γ ℓ → Type (Γ ,, σ) ℓ
>> -}
>> {-
>>   Aℕy-form : ∀ {N} (Γ : Context N) → Type Γ zero
>>   Aℕy-form [] = ℕ-form
>>   Aℕy-form (Γ ,, σ) = Γ-cumul σ (Aℕy-form Γ)
>>
>>   Uni-form : {N : Nat} (Γ : Context N) (ℓ : Nat) → Type Γ (suc ℓ)
>>   Uni-form [] _ = 𝒰-form _
>>   Uni-form (Γ ,, γ) _ = {!Γ-cumul (Uni-form Γ _) γ!}
>> -}
>>   -- Vble isn't really a term former, but rather a derivation
>>   data Variable : {N : Nat} → Context N → Fin N → Set where
>>     zero : {N : Nat} (Γ : Context N) {ℓ : Nat} (γ : Type Γ ℓ) → Variable (Γ ,, γ) zero
>>   data Term where
>>
>>   data Equation where
>>
>>     --
>>     -- ℕ-zero : Term
>>     -- variable : {N : Nat} (Γ : Context N) → (v : Fin N) → Variable Γ v → Term Γ (
>>     -- ctxHead : {N : Nat} {Γ : Context N} {ℓ : Nat} (A : Type Γ ℓ) → Term (Γ ,, A) A
>>   {-
>>     ctxHead : {N : Nat} {Γ : Context N} {ℓ : Nat} (A : Type Γ ℓ) → Term (Γ ,, A) A
>>     weaken : {N : Nat} {Γ : Context N} {ℓ ℓ' : Nat} (σ : Type Γ ℓ) → Term Γ σ → (γ : Type Γ ℓ') → Term (Γ ,, γ) (Γ-cumul γ σ)
>>     variable' : {N : Nat} {Γ : Context N} {ℓ : Nat} → (σ : Type Γ ℓ) → Term Γ σ
>>     form-intro : {N : Nat} {Γ : Context N} {ℓ : Nat} → Type Γ ℓ → Term Γ {!(𝒰-form ℓ)!}
>>     variable : {N : Nat} {Γ : Context N} {ℓ : Nat} (A : Type Γ ℓ) → Term (Γ ,, A) (Γ-cumul A A)
>>     Π-intro : {N : Nat} {Γ : Context N} {ℓ : Nat} (A : Type Γ ℓ) (B : Type (Γ ,, A) ℓ) → Term Γ (Π-form A B)
>>     -- here is my version of Π-elim, useful in forwards reasoning
>>     Π-elim' : {N : Nat} {Γ : Context N} {ℓ : Nat} (A : Type Γ ℓ) (B : Type (Γ ,, A) ℓ)
>>               → Term _ (Π-form A B) → Term (Γ ,, A) B
>>     {-
>>     Π-elim : {N : Nat} {Γ : Context N} {ℓ : Nat} (A : Type Γ ℓ) (B : Type (Γ ,, A) ℓ)
>>              (B[a/x] :
>>              → Term Γ B[a/x]
>>     -}
>>     ℕ-intro-zero : Term [] ℕ-form
>>     ℕ-intro-succ : Term [] ℕ-form → Term [] ℕ-form
>>     -- Γ-cumul : {N : Nat} {Γ : Context N} (σ : → Term Γ σ →
>>     ℕ-elim : {N : Nat} {Γ : Context N}
>>              {ℓ : Nat} (C : Type (Γ ,, Aℕy-form Γ) ℓ)
>>                        {C₀ : Type Γ ℓ}
>>                        (c₀ : Term Γ C₀)
>>                        {Cₛ : Type (Γ ,, Aℕy-form Γ ,, C) ℓ}
>>                        (cₛ : Term (Γ ,, Aℕy-form Γ ,, C) Cₛ)
>>                        (n : Term Γ (Aℕy-form Γ))
>>                        (Cₙ : Type Γ ℓ)
>>                        {- now we need to provide assertions that
>>                           C₀ ≡ C[0/x]
>>                           Cₛ ≡ C[succ x/x]
>>                           Cₙ ≡ C[n/x]
>>                        -}
>>              → Term Γ Cₙ
>>   -}
>> ` ``
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

But wait, there's trouble when forming a context. See the rule ctx-EXT (or actually any rule which assumes that a given term is judged to live in a certain universe). So, there that's why we /do/ need this separate notion of a proposition. So, contexts are built-up by `Type`s, which are built by `Context`s, and Vble shows us that a `Term` is built also by a `Context`. But it's like I want to say that that `Term` generated by Vble can also stand (sometimes) as a `Type`. That is, when the Aᵢ happens to be a universe. So what we have so far are:

Context N ≝ there is a list of assertions of size N
Type Γ ℓ ≝ there is an assertion that is formable in the universe-of-discourse ℓ and that assumes everything listed in the list of assertions Γ
Term τ ≝ there is a proof of the assertion τ

Now what we want is to be able to say that certain proofs are also assertions (certain others are, I guess, ostentions---e.g. zero!). We want then whenever the judgement Γ ⊢ a : A is such that A is a universe 𝒰ᵢ. That is, if we have it that Γ ⊢ A ≡ 𝒰ᵢ : B. Let's reformulate and add.

-- okay, wait. An assertion may be made on a background of assumptions. So the assertion depends on this background. Let's call the assertion /itself/ the statement and call the ... But could we have it that we have an If the background is a list of ...

We might have it that Γ , P ⊢ Q and Γ , ¬ P ⊢ Q. Then (classically) we would conclude Γ ⊢ Q. Does this work intuitionistically?

```agda
module TestIntuition where
  open Preliminary
  classically-valid : (P Q : Set) → (P → Q) → (¬ P → Q) → Q
  classically-valid P Q onlyifP onlyif¬P = onlyif¬P {!!} -- but not valid intuitionistically
```

ℓ ≔ Universe
∙,Γ,Δ ≔ Background N ≝ there is a list of assertions of size N
τ,γ ≔ Assertion Γ ℓ ≝ there is an assertion that is formable in the universe-of-discourse ℓ and that assumes everything listed in the list of assertions Γ
x,y,z ≔ Proof τ ≝ there is a proof of the assertion τ
Equation x y ≔ proofs x and y are equivalent
Subsumes τ γ ≔ τ is based on strictly fewer assumptions than γ, and is otherwise equivalent
AssertionInBackgroundAtIndex Γ γ i ≔ the assertion γ exists in Γ



We also have some constructors

data Universe : Set where
  zero : Universe
  suc : Universe → Universe

data Background : Nat → Set where
  [] : Background zero
  _,,_ : ∀ {N} (Γ : Background N) {ℓ} (γ : Assertion Γ ℓ) → Background (suc N)

data Assertion : ∀ {N} (Γ : Background N) (ℓ : Universe) → Set   where
  weaken : Assertion (Γ ,, τ) ℓ → Assertion (Γ ,, τ) ℓ

data AssertionInBackgroundAtIndex
  (
  where
  here : ∀ Γ γ → AssertionInBackgroundAtIndex (Γ ,, γ) γ 0
  there : AssertionInBackgroundAtIndex Γ γ 0

data Proof where
  vble : ∀ {N} (Γ : Background N) (i : Fin N)
       → AssertionInBackgroundAtIndex
  vbleₙ : ∀ {N} (Γ : Background N) (τ : Assertion Γ ℓ)
        → Proof τ

  weaken : ∀ {N} {Γ : Background N} {γ : Assertion Γ ℓ} → Proof γ → Proof

universe : (ℓ : Universe) → Proof (universe
IsAssertion x ≔



...

Let's try an approach where we build "proto" assertions and proofs, where instead of being indexed by a background containing further assertions, they are instead only indexed by the size of the background. No... that will make it too hard to express things like =-form. Maybe there's something to it, but ...

If we are going to index Assertions by a Background of Assertions, then we also need a way of saying that two Assertions are "lexicographically" equivalent. That means that they live in the same universe and that the background assertions on which they depend are also lex-equivalent. So this cuts to another idea which is that if I have ℕ : 𝒰₀, it is in some way equivalent to ℕ : 𝒰₁. But another reading of this would say that ℕ : 𝒰₀ is a subtype of ℕ : 𝒰₁ (or is it the other way around?). ⊢ ℕ : 𝒰₁ makes a weaker claim than ℕ : 𝒰₀. But if we then make further claims, we see that ⊢ zero : ℕ₁ is ...

stronger = makes fewer assumptions or makes "more" assertions P × Q is stronger than P, but Π P (λ _ → Q) is weaker than Q, though B a is weaker than Π A B.

⊢ Π A B
x : A ⊢ B x -- equal in strength to the above

⊢ Π P (λ _ → Q)
p : P ⊢ Q

{-
module TypeTheory-Try#2 where

  open Preliminary

  data Context : Nat → Set

  data _⊢_

  data Context where
-}




For every typing judgement, we can find a minimal equivalent judgement. The minimal set of suppositions required for the type of the judgement may be a subset of that required for the term, but not vice-versa. For example, in proving (A B : Set) (f : A → B) , (x : A) ⊢ f x : B, the type depends on B, but the term depends on f and x, which in turn depend on A and B.

In that case, the minimal set was exactly everything in context. However, we may have an assertion that does not need everything in context. For example,

(A B : Set) (f : A → B) , (x : A) (y : A) (C : Set) ⊢ f x : B

That does not depend on C or y (although we could have used y instead of x).

Let's try to characterise Vble.

(A B C : Set) ⊢ B : Set

I'd like the form of this judgement to be something like

variable 1 : Term ([] ,, universe 0 ,, universe 0 ,, universe 0) (universe 0)

universe 0 : Type []

so each type in the context may have a different background, and this can be okay so long as the backgrounds of each type are contained in the context so far. Notice that even the type of the term, variable 1, has a null context, although the ...

so the one with strictly more assumptions is a subtype of the one with fewer assumptions.

So we may specify a context like

data Context : Nat → Set where
  [] : Context 0
  _∷_ : ∀ {N} {Γ : Context N} {N'} {Γ' : Context N'} {ℓ} → Type Γ' ℓ → Γ ≼ Γ' → Context (suc N)

-- well, what I really mean by a subtype includes anything with a different ordering as well. So, this would need to build-up all permutations of all supersets. Maybe what is needed is to define a kernel of a context as being one with a certain canonical structure.
data _≼_ : ∀ {N N'} → Context N → Context N' → Set where
  equal : ∀ {N} (Γ : Context N) → Γ ≼ Γ
  add-something-to-lhs : ∀ {N N' N'' ℓ} {Γ : Context N} {Γ' : Context N'} → (δ' : Γ ≼ Γ')
                       → {Γ'' : Context N''} (τ : Type Γ'' ℓ) → (δ'' : Γ ≼ Γ'') → (τ ∷ δ) ≼ Γ'

data Type : ∀ {N N'} → Context N → Universe → Set

data Term : ∀ {N N'} → (Γ : Context N) (Γ' : Context N')

Think of the context as a tree structure, with each leaf being an empty context, and then types that are not dependent on anything being the innermost ...


Maybe this is too complicated.

We have `τ : Type Γ ℓ` which stands for both a judgement that there is a type of universe ℓ in context Γ and also that it stands for a construction of that type. The trouble I ran into earlier was that, as part of constructing the type, I wanted to refer to other types in the context. For example,

(P) (A : Set) (B : Set) (x : B) ⊢ B : Set

If, unlike Appendix A.2, I am going to keep separate the notions of judging something as a type of a universe and judging something as a term of a type...

well the above example is not clear... there we could read that as saying the variable B is a term of type Set, or we could read that it's saying that given certain assumptions, the type variable B is in universe 0.

On the one hand, I'd like to read it as the former: it's a term. That's what goes in places like that. It's Context ⊢ Term : Type. But then what about the B in (x : B). That's a type. But it wouldn't be there were it not for the fact that

(*) (A : Set) (B : Set) ⊢ B : Set

So, that little "B" there represents a judgement of form (*).

And how about (*) itself? Well, Set wouldn't be there unless there was a judgement of the form

(**) (A : Set) ⊢ Set : Set₁

This rabbit hole runs deep. Hence the method of reading (P) as a judgement about a type not about a term. Then the context is a list of typing judgements. But then we come to Term. As we have characterised it, Term is indexed by the context (a list of typing judgements) and a Type (a typing judgement). Now we want to construct a Term for any non-empty context by referring to one of those typing judgements and saying that this term, variable i, is of the *same* type as that one in the context. But the one in the context is more like (*), less like (P). So we need a way to fix-up the typing judgement to put it into the context we want.

I can think of two ways to go here: add a weaken constructor for Type (this would be the fixer-upper) or change the variable constructor so that it only gives the type at the end of the context and then add a weaken constructor for Term, which would turn a judgement about a term being of a certain type in a particular context into the same judgement but for an expanded context. The problem with this latter approach is that, as we currently have it, the Type according to which the Term is indexed has exactly the same context as the Term's. So, we would have to separate the context of the Term from the context of the Type of the Term, requiring that the latter context be a supertype of the former. ...then that gets complicated, so why bother? hehehe...

If we add a weaken constructor for Type then we can no longer depend on the head constructor to tell us what kind of type we are dealing with. Also, two Types might be the "same" (have the same implied context and formation), but not be propositionally equal (in the meta-theory). Thus we would need another datatype to tell us that a given Type Γ ℓ is of a certain form. So we wind up having to do a computation! Bleh. :)

Now, what if we want a Term that represents the ℕ type. For example, we want to prove a judgement

() : ℕ = ℕ : 𝒰₁

To state such a judgement, given that, on either side of the = there goes a Term, we would need constructors for the various primitive types in the Term datatype or else have a (literal-type : (τ : Type Γ ℓ) → Term Γ (universe ℓ)) constructor. That seems pretty.

So (once again) why not combine all judgements about terms being of certain types into a single datatype, such as

data TermType : (N : Nat) (Γ : Context N) (type : TermType) ...

umm, that pretty much says it. We are trying to talk about TermTypes being of a certain TermType (circular), rather than saying Terms are of certain Types, and allowing that we can construct Terms of certain Types from certain other Types, which themselves might be constructed from certain other Terms... Notice that we do *not* say that Types *are of* certain Terms (or risk circularity with the fact that Terms are of certain Types.

To review:

* we should add a literal-type constructor for Term
* we should add a weaken-context constructor for Type
* we need some (computational?) way of deciding that a given Type is of a certain type (irrespective of the weaken-context constructor)
* do we need a weaken-context for Term?
* should we allow a more generic function to weaken-context, such that we could add-in a larger context δ, and at a place in-between (instead of at the end of) the context. I.e. change Γ,Δ into Γ,δ,Δ.
* we still need to address substitutions

On the subject of the more generic weaken-context, it feels to me that this is adding too much complication to the datatype. To be more NVC: we would be making more "equivalent" Types not propositionally equal. OTOH, who cares? We've already gotten there with the simplified weaken-context constructor. In for a penny, in for a pound. If we want to avoid all that, we could create a function (a computation, oh my!) which transforms a Type Γ ℓ into a Type (Γ ,, τ) ℓ.

Of course, how would we know it was correct?! A similar story can be made about substitution: we define it, we think it's correct, it looks correct, we can verify that it meets certain requirements, but we have no language in the meta-theory to express that meets whatever standard of sufficiency (correctness) we have in mind.

So, there's a trade-off.

On the one hand, we could complicate the Type datatype by adding another constructor, thereby disconnecting it from our original meta-theoretic notion of it (as witnessed by the fact that we need to add another function to tell us if it is equivalent or not to another Type with the same context and universe level---whereas without the constructor, we can tell that they're equivalent via the meta-theoretic notion of definitional equality). But, we are quite certain that the function of applying the constructor is correct (we read it off in one line).

On the other hand, we could keep the Type datatype as simple as our meta-theoretic notion, but then add

...wait I think I was way off. Having the weaken-context constructor for Types does not make it hard to ask about equivalence. It actually makes it easier. What it does it makes it harder to tell if a Type is of a certain (meta-theoretic) type. But that's as to be expected since Type is not a type. It's a judgement about a type. It's written in a similar way to the meta-theoretic writing of a type. With weaken-context, we break this similarity? ...

There's actually a big gain to adding another constructor to Type: it allows us to simplify all the rest of the constructors, which before were doing the work of asking for a context in which to construct, say, the universe type. With the weaken-context constructor, we simply say that a universe may be formed in the null context (rather than any given context) and then say separately that from any type in a certain context is constructible such a type in an expanded context. For a fixed expansion, this is a 1-1 relation. So I don't know why anyone would complain.

The only problem is that we can no longer read-off the type of Type it is (Π, universe, etc.) from the head constructor. Now we need to peer in past the weaken-contexts to find out. Examples:

() ⊢ ℕ :𝒰 ₀
() ⊢ Π (x : ℕ) (= ℕ x x) :𝒰 ₀
(x : ℕ) ⊢ = ℕ x x :𝒰 ₀
() ⊢ Π (x : ℕ) (Π (y : ℕ) (= ℕ x y)) :𝒰 ₀ -- Type
(x : ℕ , y : ℕ) ⊢ = ℕ x y :𝒰 ₀
() ⊢ Π (x : ℕ) (Π (y : ℕ) (= ℕ x y)) : 𝒰₀ -- Term

(x : ℕ , y : ℕ) ⊢ = ℕ x y : 𝒰₀ -- Term
(x : ℕ) ⊢ ℕ :𝒰 ₀ -- the Type of the context element y in the above Term
(x : ℕ , y : ℕ) ⊢ ℕ :𝒰 ₀ -- the Type of the first argument to the = in the above Term

This latter one is constructed by two applications of weaken-context and the an ℕ-form.

Okay, now how about 𝒰-cumul? Do we not also add that as a Type constructor? If we do, then there's how we get some ambiguity wrt definitional equality, because we could either weaken context first and then weaken the level of the universe, or go the other way around.

I see a way to avoid this problem: we consider there is a BaseType and a DerivedType. In BaseType, we construct the most maximal supertypes. And in the DerivedType we add-on all the "unnecessary" weakening stuff. We could do the weakening in stages: A ContextWeakenedType and a LevelWeakenedContextWeakenedType, so that each such datatype has a canonical form.

How about a View on a Type, where the view ... well, let's consider an example.

data D : Set where
  z : D
  f : D → D
  g : D → D

We want the canonical D to have g's first, then f's, then z.

data D1 : D → Set where
  z : D1 z
  f : (x : D) → D1 x → D1 (f x)

-- V d1 d2 = d2 is a canonical version of d1
data V : D → D → Set where
  z : V z z
  f : (x y : D) → V x y → V (f x) (f y)
  f∘g : (x y : D) → V x y → V (f (g x)) (g (f y))
  g : (x y : D) → V x y → V (g x) (g y)

Then V (f (g (f z))) (g (f (f z))) has the following structure:

g (f z) -- nope, this will not build-up

f∘g (f z) -- built-up from the outside

How about V (f (g (f (g (f z))))) (g (g (f (f (f z)))))??

No, we cannot build this one. from either direction.


>>>>>>>>>>>>ERR
>> That looks like it would work. So probably we could make a View type for Type that canonicalises it. But then there's Term. Because Context and Type and Term are mutually defined, we would need View types for Context and Term as well. In the Type, we refer to Term.
>>
>> We will have a similar loopiness if we define functions that examine the structure of the Type, say, and tell us (for purposes of defining constructors for Term) if the type is a Π-form or ℕ-form or what. So, I don't see why
>>>>>>>>>>>>>>>>>>

Let's try another approach.

data CanonicalD : Nat → Nat → Set where -- indexed by the number of f's and g's in the finished product
  z : CanonicalD 0 0
  f : ∀ m n → CanonicalD m n → CanonicalD (suc m) n
  g : ∀ m n → CanonicalD m n → CanonicalD m (suc n)

data Z-core : D → Set where
  z : Z-core z

data F-inner-shell : D → Set where
  z : (d : D) → Z-core d → F-inner-shell d
  f : (d : D) → F-inner-shell d → F-inner-shell (f d)

data G-outer-shell : D → Set where
  fz : (d : D) → F-inner-shell d → G-outer-shell d
  g : (d : D) → G-outer-shell d → G-outer-shell (g d)

Notice that we could have built-up the G-outer-shell without D, so our existing G-outer-shell is like a view of that simpler datatype with D.

Recall our last review:


To review:

* we should add a literal-type constructor for Term
* we should add a weaken-context constructor for Type
* we need some (computational?) way of deciding that a given Type is of a certain type (irrespective of the weaken-context constructor)
* do we need a weaken-context for Term?
* should we allow a more generic function to weaken-context, such that we could add-in a larger context δ, and at a place in-between (instead of at the end of) the context. I.e. change Γ,Δ into Γ,δ,Δ.
* we still need to address substitutions

I think we should have a weaken-context for Term for one of the same reasons that it's nice to have the same for Type: it allows us to describe certain judgements of terms being inhabitants of types without also having to say "and this can be done in any weakened context".

I don't think we need the more generic version of weaken-context *yet*. The philosophy is going to be (for now) to write the datatypes with constructors as simple as possible, but with as many constructors as needed.

I'd like to view this from an opposite perspective now: consider the lexical form of a typing judgement ...

Umm, really not sure where I was going with that. I am still not clear on at least a couple of things:

* substitutions
* variables (in terms or types)

Because of the mutual definition of Context, Term, and Type, I think it's safe to say that they really, all together, represent something else (something as yet unnamed, and perhaps unnameable in the meta-theory (Agda)).

If we create functions to identify whether, say, a given Type is Π or ℕ, then I guess we would also create functions to transform a Type in a way that variables internal to it are substituted. Alternatively, we create some other datatype, say IsPi : ∀ {ℓ N Γ} → Type Γ ℓ → (A : Type Γ ℓ) → Type (Γ ,, A) ℓ → Set. For example, I'm thinking that Π-elim, as a constructor for Term, would have a form such as this:

Π-elim : ∀ {ℓ N} {Γ : Context N} {ΠAB : Type Γ ℓ} {A : Type Γ ℓ} {B : Type (Γ ,, A) ℓ}
       → IsPi ΠAB A B
       → (f : Term Γ ΠAB)
       → (a : Term Γ A)
       → (B[a/x] : Type Γ ℓ)
       → IsSubstitution B[a/x] B a zero
       → Term Γ B[a/x]

But then what of substitutions of terms in types that contain terms that are derived via, say, Π-elim? IsSubstitution would have to "know" about elimination rules, but the usual description of a substitution involves only variable-laden terms. The trouble again is that Term is really saying that "there is a proof (derivation, construction) of a Type", where Type is really saying "there is a proof of an inhabitant of a universe". If substitute, say, x for succ x in a Type, keeping the context fixed, we are really asking for a proof of a different inhabitant of

example

ΠAB == (c x : ℕ) ⊢ Π (y : ℕ) (x = y) :𝒰 0
A == (c x : ℕ) ⊢ ℕ :𝒰 0
B == (c x y : ℕ) ⊢ x = y :𝒰 0
f == (c x : ℕ) ⊢ f : Π (y : ℕ) (x = y)
a == (c x : ℕ) ⊢ c : ℕ
B[a/x] == (c x : ℕ) ⊢ x = c :𝒰 0

no, I think this is workable. When we substitute within a type that contains a term constructed by Π-elim

e.g. say our type contains the expression, f x = y, where x is free and we want to replace it with f y. Then our type contains a reference to a free variable, and it is found within a constructor Π-elim, as a Term (in fact, (a : Term ...)). B[a/x] has the type with containing the expression f (f y) = y. IsSubstitution just checks that whenever B contains a particular variable, B[a/x] contains the term `a`, and otherwise the structures are the same. The structure of B will be smaller because it has strictly more variables.

Okay, so it works. Interesting that IsSubstitution has a functional structure: for any given "inputs" B a zero, there is exactly one possible IsSubstitution structure for B[a/x] (right?). And it's semi-composable, b/c if we do [y/x][z/y], we get the same as [z/x] (except that we would then drop y). Anywhoo, it seems like we could just as well have written a function to do the job. And, given that IsSubstition is indeed functional, we can write a function that takes B and a as inputs and outputs a B[a/x], along with a proof that such a thing IsSubstitution.

It seems silly to define such functions. How about things like ≼, where the rhs defines a supertype? If we wanted a maximal version of it, so that the rhs means that it is not only with fewer premises, but has the fewest premises possible and still be the "same", then we could just write a maximizing function. So ≼ is a perfectly fine, non-stupid, non-functional datatype precisely because it is not functional.


I want to review where I'm at again.

* I believe I have enough to write the type theory, including such datatypes as

  * ℓ : Universe -- all universes of discourse (really, I'm not quite sure what that means)
  * Γ : Context N -- all ordered N-length lists of assertions
  * τ : Type Γ ℓ -- all assertions regarding objects of universe ℓ under the suppositions Γ
  * ρ : Term τ -- all proofs of the assertion τ

and such functions as

  * apType : (τ : Type (Γ ,, γ)) → Term γ → Type Γ
  * apTerm : {τ : Type (Γ ,, γ)} → (ρ : Term γ) → Term (apType τ ρ)

Therefore, what? Can I make the following claims?

consistent : ¬ Term 𝟘
decidable : ∀ {ℓ} {τ : Type [] ℓ} → ¬ ¬ Term τ → Term τ

Probably yes for `consistent`. Probably no for `decidable` (due to both Π and ℕ). What about a weaker claim?

decidable₀ : ∀ {τ : Type [] 0} → ¬ ¬ Term τ → Term τ

Probably not even that, due to ℕ.

With universes unrestricted, Π is allowed to quantify over quantifications. With the restriction to universe 0, we can are beset by ℕ-elim increasing the complexity of the assertion of interest.

Some further questions

  1. Could I create a universe -1 such that infinite types such as ℕ were ruled-out? Could I then achieve decidability?
  2. Could I define FinTerm τ n, all proofs of the assertion τ that take less than n steps? Would that not then be decidable? Or, in the case of universe 0, letting n be the number of invocations of ℕ-elim?
  3. What does it mean to say that type-checking is decidable? Surely not the obvious, ∀ {ℓ} → ¬ ¬ Type [] ℓ → Type [] ℓ?
  4. I characterise completeness as follows: a procedure which, given any provable assertion, eventually provides the proof. Is there some way to write this characterisation in Agda?
    >>> ERR
    >> sound : ∀ {ℓ} (τ : Type [] ℓ) n → FinTerm τ n → Term τ
    >> complete : ∀ {ℓ} (τ : Type [] ℓ) n → ¬ ¬ FinTerm τ n → FinTerm τ n
    >>>
    no, these are not what I'm looking for. Completeness is relative to a semantics. In FOL, it is characterised as "validity".
    for a made-to-order proof theory (say, what I imagine developing with a la Natural Deduction), what I want is this:
      decidable : ∀ {ℓ} (τ : Type [] ℓ) n → ¬ ¬ FinTerm τ n → FinTerm τ n
      complete : ∀ {ℓ} (τ : Type [] ℓ) → Term τ → ∃ λ n → FinTerm τ n
      consistent : ¬ ∃ λ n → FinTerm 𝟘 n
      sound : ∀ {ℓ} (τ : Type [] ℓ) n → FinTerm τ n → Term τ
    What I will never get is this:
      magic₁ : ∀ {ℓ} (τ : Type [] ℓ) → ¬ ¬ ∃ λ n → FinTerm τ n → ∃ λ n → FinTerm τ n
    or even this:
      magic₂ : ∀ {ℓ} (τ : Type [] ℓ) → ¬ (∀ n → ¬ FinTerm τ n) → ∃ λ n → FinTerm τ n
  5. What about prob and defeasible reasoning?
  6. How about completeness relative to other semantics, such as homotopies or sheafs?
  7. How do I imagine this interactive proof system?

As for prob, I have an intuition that, though P ∨ ¬ P is not provable in the intuitionistic type theory, we could characterise that prob (P / P ∨ ¬ P) = 0.5. In Probable Probabilities, P is a set, but here, it is a type or `Assertion`. Also, in John's thinking, we talk about prob (P / U), but that equates to prob (P ∩ U / U). The point is that the lhs is contained in the rhs. We could look at it then as prob ((P ∨ ¬ P) → P). So, when P and Q are types, prob (P / Q) = PROB (Q → P). or something, i dunno.

Oscar has parameters that tell it how much to reduce interest during stages of backwards reasoning. John's intuition may have been that it gets less likely that longer chains of backwards reasoning would find the solution than shorter parallel ones that followed a different strategy. I think this is characterisable, justifiable in terms of probable probabilities.

It's time to build the type theory.

```agda
module A2TT where

  open Preliminary

  Universe = Nat
  Complexity = Nat
  data Background : Nat → Set
  data Assertion {N} (Γ : Background N) : Universe → Set
  data Evidence : ∀ {N} {Γ : Background N} {ℓ} → Assertion Γ ℓ → Complexity → Set

  infixl 5 _,,_

  data Background where
    [] : Background zero
    _,,_ : ∀ {N} (Γ : Background N)
         → ∀ {ℓ} (τ : Assertion Γ ℓ)
         → Background (suc N)



  data Assertion {N} (Γ : Background N) where
    `Set : (ℓ : Universe) → Assertion Γ (suc ℓ)
    `𝟘 `𝟙 `ℕ : Assertion Γ zero
    `= : ∀ {ℓ} (τ : Assertion Γ ℓ)
         → ∃ Evidence τ → ∃ Evidence τ
         → Assertion Γ zero
    `∨ : ∀ {ℓ}
         → Assertion Γ ℓ
         → Assertion Γ ℓ
         → Assertion Γ ℓ
    `∀ `Σ : ∀ {ℓ}
              (π : Assertion Γ ℓ)
            → Assertion (Γ ,, π) ℓ
            → Assertion Γ ℓ
    evidence : ∀ {ℓ}
      → ∃ Evidence {Γ = Γ} (`Set ℓ)
      → Assertion Γ ℓ
      {-
    recall : ∀ {ℓ}
             → (v : Fin N)
             → backgroundUniverse Γ v ≡ suc ℓ
             → Assertion Γ (suc ℓ)
-}
    transcend :
      ∀ {ℓ}
      → Assertion Γ ℓ
      → Assertion Γ (suc ℓ)

  data Evidence where
    {-
    stipulate : ∀ {N} {Γ : Background N} {ℓ}
                {τ : Assertion Γ ℓ}
                {χ} → Evidence τ χ
                → Evidence
    -}

-- variable : ∀ {N} {Γ : Background N} {ℓ}

               -- → Evidence {!!} {!!}
  {-
    variable : ∀ {N} {Γ : Background N} {ℓ}
               → backgroundUniverse ℓ
               → Evidence Γ τ
  -}
    -- well, I said it, didn't I?
    {-
    assertion : ∀ {N} {Γ : Background N} {ℓ}
                → (τ : Assertion Γ ℓ)
                → Evidence (stipulate τ) zero
    -}

  module TestAssertiveness where

    -- () ⊢ Π (A : 𝒰₀) Π (n : ℕ) (A + (n = n)) : 𝒰₁
    -- for all assertions about objects, A, and all numbers, n, either A is true or n equals n
    test-1 : Assertion [] (suc zero)
    test-1 = `∀ (`Set zero) (`∀ (transcend `ℕ) (`∨ {!!} (transcend (`= {!!} {!!} {!!})))) -- `∀ (`Set zero) (`∀ (transcend `ℕ) (`∨ {!!} (transcend {!!})))

    -- () ⊢ ℕ : 𝒰₀
    there-are-numbers : Assertion [] zero
    there-are-numbers = `ℕ

    -- () ⊢ ℕ : 𝒰₁
    there-arrre-numbers : Assertion [] (suc zero)
    there-arrre-numbers = transcend `ℕ

    -- (_ : ℕ) ⊢ ℕ : 𝒰₀
    given-there-is-a-number-then-there-are-numbers : Assertion ([] ,, `ℕ) zero
    given-there-is-a-number-then-there-are-numbers = {!!} -- stipulate `ℕ

    -- (_ : ℕ) ⊢ ℕ : 𝒰₁
    given-there-is-a-number-then-there-really-arrre-numbers : Assertion ([] ,, `ℕ) (suc zero)
    given-there-is-a-number-then-there-really-arrre-numbers = {!!} -- transcend (stipulate `ℕ)

    -- () ⊢ Π (_ : ℕ) Π (_ : ℕ) ℕ : 𝒰₀
    addition : Assertion [] zero
    addition = {!!} -- `∀ `ℕ (`∀ (stipulate `ℕ) (stipulate (stipulate `ℕ)))

    -- () ⊢ 𝒰₀ : 𝒰₁
    people : Assertion [] (suc zero)
    people = `Set zero

    -- () ⊢ 𝒰₀ : 𝒰₁
    natural-numbers : Assertion [] (suc zero)
    natural-numbers = `Set zero

    -- (_ : 𝒰₀) ⊢ 𝒰₀ : 𝒰₁
    zeroness : Assertion ([] ,, natural-numbers) (suc zero)
    zeroness = {!!} -- stipulate (`Set zero)

    -- (NN : 𝒰₀) (Z : NN) ⊢ NN : 𝒰₀
    succer : Assertion ([] ,, natural-numbers) zero
    succer = `∀ {!!} {!!}

    -- () ⊢ Π (A : 𝒰₀) A : 𝒰₁
    everything-is-inhabited : Assertion [] (suc zero)
    everything-is-inhabited = `∀ (`Set 0) {!!} -- `∀ (`Set 0) (`∀ (stipulate {!!}) {!stipulate!})

    {-
    -- () ⊢ Π (NN : 𝒰₀)
              Π (PA : Σ (Z : NN) Σ (S : Π (nn : NN) NN))
    -}

```

I'm having difficulty with interpreting A.2 and am going in circles. The next attempt is inspired by A.1.

```agda
module A1TT where

  open Preliminary

  data Variable : Set where
  data PrimitiveConstant : Set where
  data DefinedConstant : Set where
  data Term : Set where
    variable : Variable → Term
    abstraction : Variable → Term → Term
    application : Term → Term → Term
    primitive-constant : PrimitiveConstant → Term
    defined-constant : DefinedConstant → Term
  data DefiningEquation : DefinedConstant → Set where
```

I'll come back to that maybe. I have an idea that the Evidence can be indexed by a term. I have been troubled by the fact that it seemed that Evidence was serving a dual role of rule application and term representation. The "term" will be a more lexicographic structure---what we actually write in programs. Then the idea is that Assertion can also be ... okay, I should make clear what is actually the matter with the first approach.

I tried to do a number of things that turned out to be somehow incompatible:

* Make `Assertion` the kind of data structure that could be represented without appealing to derivations. It is intended to represent alleged theorems.
* Make `Evidence` the represent (correct, not alleged) theorems.

The fact that `Evidence` turned out to be part of the data structure of `Assertion` (for the definition of identity) was thought to be compatible (and maybe it is) with the above aims: the idea is that, for a theorem to type-check, terms given to identity must be of the appropriate type.

* Make `Assertion` represent the form of judgement, Γ ⊢ ASSERTION : 𝒰ᵢ. So, like `Evidence`, in addition to representing something as well as proving it, `Assertion` represents a type and a proof that the type really is a type (because it lies in some universe---so stop lying!).

* Make `Background` represent a (possibly dependent) list of assertions.

So consider the following assertions:

() ⊢ ℕ : 𝒰₀  -- ℕ is in the first universe, an assertion made without anything in the background
(() ⊢ ℕ : 𝒰₀) ⊢ ... -- some assertion that relies on the above assertion being in the background
(x : ℕ) ⊢ ... -- the same as above, but written differently ... so, when we put something in the background, we get to assume that it is inhabited, so we get to refer to the evidence for the small price of stating the variable.
() ⊢ Π (x : ℕ) ... -- Π takes two arguments: the first is an assertion, the second some assertion that is made with the first argument as part of its background. So, we get to assume that ℕ is inhabited in the "..."
() ⊢ Π (x : ℕ) x -- this is not well-formed (or, rather, it should not be)
() ⊢ Π (A : 𝒰₀) A -- this is well-formed.

The trouble came when trying to make `Assertion` support the last two expressions properly. In the second argument to Π, I took it that it had to check-out as an Assertion in a context expanded by the first argument. I had to have some way of referring to a part of the background via a "variable". At first, I took it that this variable, as it denotes an Assertion in the Background, must itself *be* an assertion. That resulted in being able to say nonsense like "() ⊢ Π (x : ℕ) x".

So, I would like some way of constructing an Assertion in which I give a reference to a variable in the background, but only in such manner as that assertion in the background is inhabited by assertions. Before I go off with another alleged solution, consider the following trickiness.

(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) ⊢ Π (F : Π (x : A) (B x)) (= (B a) (F a) (Ba)) : 𝒰₀

The application, B a is unrepresentable in the current system, though it is a perfectly fine type.

In the background, I can regard each item to the right of the ":" as Evidence of 𝒰ᵢ. So, that's what a type is. Then in the expression "(Ba : B a)", "B a" is Evidence of 𝒰₀ and "a" is Evidence of A, which is Evidence of 𝒰₀.

A derivation (which feels to me like type-checking):

⊢ 𝒰₀ : 𝒰₁
A new-variable
(A : 𝒰₀) ctx
(A : 𝒰₀) ⊢ A : 𝒰₀ -- assertion
x new-variable
(A : 𝒰₀) (x : A) ctx
(A : 𝒰₀) (x : A) ⊢ 𝒰₀ : 𝒰₁ -- assertion
------------------------------
(A : 𝒰₀) ⊢ Π (x : A) 𝒰₀ : 𝒰₁


⊢ 𝒰₀ : 𝒰₁
A new-variable
(A : 𝒰₀) ctx
(A : 𝒰₀) ⊢ A : 𝒰₀
x new-variable
(A : 𝒰₀) (x : A) ctx
(A : 𝒰₀) (x : A) ⊢ 𝒰₀ : 𝒰₁

(A : 𝒰₀) ⊢ Π (x : A) 𝒰₀ : 𝒰₁

B new-variable
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) ctx
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) ⊢ A : 𝒰₀
a new-variable
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) ctx
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) ⊢ a : A -- this is not an assertion
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) ⊢ B : Π (x : A) 𝒰₀
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) ⊢ B a : 𝒰₀[a/x]
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) ⊢ B a : 𝒰₀ -- this is an assertion
Ba new-variable
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) ctx
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) ⊢ A : 𝒰₀
x new-variable
-------------------
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) (x : A) ⊢ A : 𝒰₀

(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) ⊢ B : Π (x : A) 𝒰₀
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) ⊢ a : A --
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) ⊢ B a : 𝒰₀[a/x]
(A : 𝒰₀) (B : Π (x : A) 𝒰₀) (a : A) (Ba : B a) ⊢ B a : 𝒰₀ -- assertion

notice how the assertion is at the root of a (derivation) tree

Let's see if we can list all the well-formed types (the things that go to the right of ":", given well-formed context. well, no, that takes all of type theory.

>>>>>>>>>>>>>>>>>>>>>>>>> ERR
>> Let's try to spell out how the above tricky sentence gets constructed.
>>
>> Let A, B, x, a, Ba, F be variables. Let 𝒰₀ be the universe of level 0. Let 𝒰₁ be the universe of level 0.
>>
>> Bring A into scope and let it denote 𝒰₀.
>>
>> See that 𝒰₀ inhabits 𝒰₁.
>>
>> Form the Π expression in 𝒰₁ by quantifying with binding variable x over A into 𝒰₀
>>
>> Bring x into scope and let it denote A.
>>
>> Bring B into scope a let it denote
>>
>> background
>>
>> 𝒰₀ universe
>> A variable
>> A : 𝒰₀ postulate
>> --------------------
>> (A : 𝒰₀) background
>>
>> x variable
>> A : 𝒰₀ postulate
>> (x : A)
>>
>> ... ugh, that is getting me nowhere.
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

Next attempt:

```agda
module A2TT′ where

  open Preliminary

  Universe = Nat
  Complexity = Nat

  data Term (N : Nat) : Set where
    𝒰 : Universe → Term N
    𝓋 : Fin N → Term N
    ΠF : Term N → Term (suc N) → Term N
    ΠI : Term (suc N) → Term N
    ΠE : Term N → Term N → Term N
    ΣF : Term N → Term (suc N) → Term N
    ΣI : Term N → Term N → Term N
    ΣE : Term (suc N) → Term (suc (suc N)) → Term N → Term N
    +F : Term N → Term N → Term N
    +IL : Term N → Term N
    +IR : Term N → Term N
    +E : Term (suc N) → Term (suc N) → Term (suc N) → Term N → Term N
    𝟘F : Term N
    𝟘E : Term (suc N) → Term N → Term N
    𝟙F : Term N
    𝟙I : Term N
    𝟙E : Term (suc N) → Term N → Term N → Term N
    ℕF : Term N
    ℕIZ : Term N
    ℕIS : Term N → Term N
    ℕE : Term (suc N) → Term N → Term (suc (suc N)) → Term N → Term N
    =F : Term N → Term N → Term N → Term N
    =I : Term N → Term N
    =E : Term (suc (suc (suc N))) → Term (suc N) → Term N → Term N → Term N → Term N

  postulate
    weaken : ∀ {N} → Term N → Term (suc N)
    apply : ∀ {N} → Term (suc N) → Term N → Fin (suc N) → Term N

  data _⊢_∶_ (N : Nat) : Term N → Term N → Set where
    𝒰I : ∀ ℓ →
      N ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
    𝒰C : ∀ {ℓ A} →
      N ⊢ A ∶ 𝒰 ℓ →
      N ⊢ A ∶ 𝒰 (suc ℓ)
    ΠF : ∀ {ℓ A B} →
      N ⊢ A ∶ 𝒰 ℓ → suc N ⊢ B ∶ 𝒰 ℓ →
      N ⊢ ΠF A B ∶ 𝒰 ℓ
    ΠI : ∀ {A b B} →
      suc N ⊢ b ∶ B →
      N ⊢ ΠI b ∶ ΠF A B
    ΠE : ∀ {f A a B} →
      N ⊢ f ∶ ΠF A B → N ⊢ a ∶ A →
      N ⊢ ΠE f a ∶ apply B a zero
    ΣF : ∀ {ℓ A B} →
      N ⊢ A ∶ 𝒰 ℓ → suc N ⊢ B ∶ 𝒰 ℓ →
      N ⊢ ΣF A B ∶ 𝒰 ℓ
    ΣI : ∀ {ℓ A a B b} →
      suc N ⊢ B ∶ 𝒰 ℓ → N ⊢ a ∶ A → N ⊢ b ∶ apply B a zero →
      N ⊢ ΣI a b ∶ ΣF A B
    ΣE : ∀ {ℓ A B C g p} →
        suc N ⊢ C ∶ 𝒰 ℓ →
        suc (suc N) ⊢ g ∶ apply (weaken (weaken C)) (ΣI (𝓋 (suc zero)) (𝓋 zero)) (suc (suc zero)) →
        N ⊢ p ∶ ΣF A B →
      N ⊢ ΣE C g p ∶ apply C p zero
    +F : ∀ {ℓ A B} →
      N ⊢ A ∶ 𝒰 ℓ → N ⊢ B ∶ 𝒰 ℓ →
      N ⊢ +F A B ∶ 𝒰 ℓ
    +IL : ∀ {ℓ A a B} →
      N ⊢ A ∶ 𝒰 ℓ → N ⊢ B ∶ 𝒰 ℓ → N ⊢ a ∶ A →
      N ⊢ +IL a ∶ +F A B
    +IR : ∀ {ℓ A B b} →
      N ⊢ A ∶ 𝒰 ℓ → N ⊢ B ∶ 𝒰 ℓ → N ⊢ b ∶ B →
      N ⊢ +IR b ∶ +F A B
    +E : ∀ {ℓ A B C c d e} →
        suc N ⊢ C ∶ 𝒰 ℓ →
        suc N ⊢ c ∶ apply (weaken C) (+IL (𝓋 zero)) (suc zero) →
        suc N ⊢ d ∶ apply (weaken C) (+IR (𝓋 zero)) (suc zero) →
        N ⊢ e ∶ +F A B →
      N ⊢ +E C c d e ∶ apply C e zero
    𝟘F : ∀ {ℓ} →
      N ⊢ 𝟘F ∶ 𝒰 ℓ
    𝟘E : ∀ {ℓ C a} →
      suc N ⊢ C ∶ 𝒰 ℓ → N ⊢ a ∶ 𝟘F →
      N ⊢ 𝟘E C a ∶ apply C a zero
    𝟙F : ∀ {ℓ} →
      N ⊢ 𝟙F ∶ 𝒰 ℓ
    𝟙I :
      N ⊢ 𝟙I ∶ 𝟙F
    𝟙E : ∀ {ℓ C c a} →
      suc N ⊢ C ∶ 𝒰 ℓ → N ⊢ c ∶ apply C 𝟙I zero → N ⊢ a ∶ 𝟙F →
      N ⊢ 𝟙E C c a ∶ apply C a zero
    ℕF : ∀ {ℓ} →
      N ⊢ ℕF ∶ 𝒰 ℓ
    ℕIZ :
      N ⊢ ℕIZ ∶ ℕF
    ℕIS : ∀ {n} →
      N ⊢ n ∶ ℕF →
      N ⊢ ℕIS n ∶ ℕF
    ℕE : ∀ {ℓ C c₀ cₛ n} →
      suc N ⊢ C ∶ 𝒰 ℓ → N ⊢ c₀ ∶ apply C ℕIZ zero → suc (suc N) ⊢ cₛ ∶ weaken (apply (weaken C) (ℕIS (𝓋 zero)) (suc zero)) →
      N ⊢ ℕE C c₀ cₛ n ∶ apply C n zero
    =F : ∀ {ℓ A a b} →
      N ⊢ A ∶ 𝒰 ℓ → N ⊢ a ∶ A → N ⊢ b ∶ A →
      N ⊢ =F A a b ∶ 𝒰 ℓ
    =I : ∀ {ℓ A a} →
      N ⊢ A ∶ 𝒰 ℓ → N ⊢ a ∶ A →
      N ⊢ =I a ∶ =F A a a
    =E : ∀ {ℓ C c A a b p} →
        suc (suc (suc N)) ⊢ C ∶ 𝒰 ℓ →
        suc N ⊢ c ∶ apply (apply (apply (weaken C) (=I (𝓋 zero)) (suc zero))
                                 (𝓋 zero) (suc zero))
                          (𝓋 zero) (suc zero) →
        N ⊢ a ∶ A →
        N ⊢ b ∶ A →
        N ⊢ p ∶ =F A a b →
        N ⊢ =E C c a b p ∶ apply (apply (apply C (weaken (weaken p)) zero) (weaken b) zero) a zero

```

My intention in the above is for `Term N` to be all the syntactic forms of terms with N variables in context, and `N ⊢ a : A` to be all the syntactic forms of typing judgements with N variables in context. Unfortunately, there is a bit of a snag because I have no rule for Vble. So the following isn't inhabited:

    test : zero ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F
    test = ΠI ??

I'll try adding Vble:

```agda
    Vble :
      ∀ n {A} →
      N ⊢ 𝓋 n ∶ A
  module TestYourJudgement where
    test : zero ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F
    test = ΠI (Vble zero)

```

Well, it can't quite work. Or rather, it works way too well. The trouble is that the context such as I have coded it is simply a natural number, with no further structure to identify the syntactic form of the types contained therein.

This brings to mind an easy fix: change the representation of context in _⊢_∶_ from Nat to a dependent list of `Term`s. Well, there's a problem with that: we don't want the context to include just any ol' `Term` (they aren't well-formed). So, instead, I can try mutually-defined datatypes, one for the ctx judgement and another for _⊢_∶_. (And if this helps, I'll probably be adding one for _⊢_≡_∶_ next.)

```agda
module A2TT′′ where

  open Preliminary

  Universe = Nat
  Complexity = Nat

  data Term (N : Nat) : Set where
    𝒰 : Universe → Term N
    𝓋 : Fin N → Term N
    ΠF : Term N → Term (suc N) → Term N
    ΠI : Term (suc N) → Term N
    ΠE : Term N → Term N → Term N
    ΣF : Term N → Term (suc N) → Term N
    ΣI : Term N → Term N → Term N
    ΣE : Term (suc N) → Term (suc (suc N)) → Term N → Term N
    +F : Term N → Term N → Term N
    +IL : Term N → Term N
    +IR : Term N → Term N
    +E : Term (suc N) → Term (suc N) → Term (suc N) → Term N → Term N
    𝟘F : Term N
    𝟘E : Term (suc N) → Term N → Term N
    𝟙F : Term N
    𝟙I : Term N
    𝟙E : Term (suc N) → Term N → Term N → Term N
    ℕF : Term N
    ℕIZ : Term N
    ℕIS : Term N → Term N
    ℕE : Term (suc N) → Term N → Term (suc (suc N)) → Term N → Term N
    =F : Term N → Term N → Term N → Term N
    =I : Term N → Term N
    =E : Term (suc (suc (suc N))) → Term (suc N) → Term N → Term N → Term N → Term N

  postulate
    weaken : ∀ {N} → Term N → Term (suc N)
    apply : ∀ {N} → Term (suc N) → Term N → Fin (suc N) → Term N

  data _ctx : Nat → Set
  data _⊢_∶_ {N : Nat} (Γ : N ctx) : Term N → Term N → Set

  infixl 25 _,,_
  data _ctx where
    [] : zero ctx
    _,,_ : ∀ {N} → N ctx → Term N → suc N ctx

  _at_ : ∀ {N} → N ctx → Fin N → Term N
  (Γ ,, γ) at zero = weaken γ
  (Γ ,, _) at suc n = weaken (Γ at n)

  data _⊢_∶_ {N : Nat} (Γ : N ctx) where
    𝒰I : ∀ ℓ →
      Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
    𝒰C : ∀ {ℓ A} →
      Γ ⊢ A ∶ 𝒰 ℓ →
      Γ ⊢ A ∶ 𝒰 (suc ℓ)
    ΠF : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ,, A ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΠF A B ∶ 𝒰 ℓ
    ΠI : ∀ {A b B} →
      Γ ,, A ⊢ b ∶ B →
      Γ ⊢ ΠI b ∶ ΠF A B
    ΠE : ∀ {f A a B} →
      Γ ⊢ f ∶ ΠF A B → Γ ⊢ a ∶ A →
      Γ ⊢ ΠE f a ∶ apply B a zero
{-
    ΣF : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → suc Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΣF A B ∶ 𝒰 ℓ
    ΣI : ∀ {ℓ A a B b} →
      suc Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ apply B a zero →
      Γ ⊢ ΣI a b ∶ ΣF A B
    ΣE : ∀ {ℓ A B C g p} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc (suc Γ) ⊢ g ∶ apply (weaken (weaken C)) (ΣI (𝓋 (suc zero)) (𝓋 zero)) (suc (suc zero)) →
        Γ ⊢ p ∶ ΣF A B →
      Γ ⊢ ΣE C g p ∶ apply C p zero
    +F : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ +F A B ∶ 𝒰 ℓ
    +IL : ∀ {ℓ A a B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ +IL a ∶ +F A B
    +IR : ∀ {ℓ A B b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ b ∶ B →
      Γ ⊢ +IR b ∶ +F A B
    +E : ∀ {ℓ A B C c d e} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (weaken C) (+IL (𝓋 zero)) (suc zero) →
        suc Γ ⊢ d ∶ apply (weaken C) (+IR (𝓋 zero)) (suc zero) →
        Γ ⊢ e ∶ +F A B →
      Γ ⊢ +E C c d e ∶ apply C e zero
    𝟘F : ∀ {ℓ} →
      Γ ⊢ 𝟘F ∶ 𝒰 ℓ
    𝟘E : ∀ {ℓ C a} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ a ∶ 𝟘F →
      Γ ⊢ 𝟘E C a ∶ apply C a zero
-}
    𝟙F : ∀ {ℓ} →
      Γ ⊢ 𝟙F ∶ 𝒰 ℓ
    𝟙I :
      Γ ⊢ 𝟙I ∶ 𝟙F
    𝟙E : ∀ {ℓ C c a} →
      Γ ,, 𝟙F ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c ∶ apply C 𝟙I zero → Γ ⊢ a ∶ 𝟙F →
      Γ ⊢ 𝟙E C c a ∶ apply C a zero
{-
    ℕF : ∀ {ℓ} →
      Γ ⊢ ℕF ∶ 𝒰 ℓ
    ℕIZ :
      Γ ⊢ ℕIZ ∶ ℕF
    ℕIS : ∀ {n} →
      Γ ⊢ n ∶ ℕF →
      Γ ⊢ ℕIS n ∶ ℕF
    ℕE : ∀ {ℓ C c₀ cₛ n} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c₀ ∶ apply C ℕIZ zero → suc (suc Γ) ⊢ cₛ ∶ weaken (apply (weaken C) (ℕIS (𝓋 zero)) (suc zero)) →
      Γ ⊢ ℕE C c₀ cₛ n ∶ apply C n zero
    =F : ∀ {ℓ A a b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ A →
      Γ ⊢ =F A a b ∶ 𝒰 ℓ
    =I : ∀ {ℓ A a} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ =I a ∶ =F A a a
    =E : ∀ {ℓ C c A a b p} →
        suc (suc (suc Γ)) ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (apply (apply (weaken C) (=I (𝓋 zero)) (suc zero))
                                 (𝓋 zero) (suc zero))
                          (𝓋 zero) (suc zero) →
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ A →
        Γ ⊢ p ∶ =F A a b →
        Γ ⊢ =E C c a b p ∶ apply (apply (apply C (weaken (weaken p)) zero) (weaken b) zero) a zero

-}

    Vble :
      ∀ n A →
      Γ at n ≡ A →
      Γ ⊢ 𝓋 n ∶ A
  module TestYourJudgement where
    test : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (weaken 𝟙F)
    test = ΠI (Vble zero (weaken 𝟙F) refl)

{- this also works
    Vble :
      ∀ n → (Γ' : N ctx) → Γ' ≡ Γ →
      Γ ⊢ 𝓋 n ∶ (Γ' at n)
  module TestYourJudgement where
    test : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (weaken 𝟙F)
    test = ΠI (Vble zero ([] ,, 𝟙F) refl)
-}
```

It looks like it works a lot better now. The above commented-out version is a fair representation of the derivation in A.2, but I have a worry. Ah, the problem is that I did not really mutually define _ctx with _⊢_∶_, and wound-up taking any not-so-well-formed `Term`.

```agda
module A2TT′*3 where

  open Preliminary

  Universe = Nat
  Complexity = Nat

  data Term (N : Nat) : Set where
    𝒰 : Universe → Term N
    𝓋 : Fin N → Term N
    ΠF : Term N → Term (suc N) → Term N
    ΠI : Term (suc N) → Term N
    ΠE : Term N → Term N → Term N
    ΣF : Term N → Term (suc N) → Term N
    ΣI : Term N → Term N → Term N
    ΣE : Term (suc N) → Term (suc (suc N)) → Term N → Term N
    +F : Term N → Term N → Term N
    +IL : Term N → Term N
    +IR : Term N → Term N
    +E : Term (suc N) → Term (suc N) → Term (suc N) → Term N → Term N
    𝟘F : Term N
    𝟘E : Term (suc N) → Term N → Term N
    𝟙F : Term N
    𝟙I : Term N
    𝟙E : Term (suc N) → Term N → Term N → Term N
    ℕF : Term N
    ℕIZ : Term N
    ℕIS : Term N → Term N
    ℕE : Term (suc N) → Term N → Term (suc (suc N)) → Term N → Term N
    =F : Term N → Term N → Term N → Term N
    =I : Term N → Term N
    =E : Term (suc (suc (suc N))) → Term (suc N) → Term N → Term N → Term N → Term N

  postulate
    weaken : ∀ {N} → Term N → Term (suc N)
    apply : ∀ {N} → Term (suc N) → Term N → Fin (suc N) → Term N

  data _ctx : Nat → Set
  data _⊢_∶_ {N : Nat} (Γ : N ctx) : Term N → Term N → Set

  infixl 25 _,,_
  data _ctx where
    [] : zero ctx
    _,,_ : ∀ {N ℓ A} → (Γ : N ctx) → Γ ⊢ A ∶ 𝒰 ℓ → suc N ctx

  _at_ : ∀ {N} → N ctx → Fin N → Term N
  _,,_ {A = A} Γ γ at zero = weaken A
  (Γ ,, _) at suc n = weaken (Γ at n)

  data _⊢_∶_ {N : Nat} (Γ : N ctx) where
    𝒰I : ∀ ℓ →
      Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
    𝒰C : ∀ {ℓ A} →
      Γ ⊢ A ∶ 𝒰 ℓ →
      Γ ⊢ A ∶ 𝒰 (suc ℓ)
    ΠF : ∀ {ℓ A B} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) → Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΠF A B ∶ 𝒰 ℓ
    ΠI : ∀ {ℓ A b B} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      Γ ,, ⊢A ⊢ b ∶ B →
      Γ ⊢ ΠI b ∶ ΠF A B
    ΠE : ∀ {f A a B} →
      Γ ⊢ f ∶ ΠF A B → Γ ⊢ a ∶ A →
      Γ ⊢ ΠE f a ∶ apply B a zero
{-
    ΣF : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → suc Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΣF A B ∶ 𝒰 ℓ
    ΣI : ∀ {ℓ A a B b} →
      suc Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ apply B a zero →
      Γ ⊢ ΣI a b ∶ ΣF A B
    ΣE : ∀ {ℓ A B C g p} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc (suc Γ) ⊢ g ∶ apply (weaken (weaken C)) (ΣI (𝓋 (suc zero)) (𝓋 zero)) (suc (suc zero)) →
        Γ ⊢ p ∶ ΣF A B →
      Γ ⊢ ΣE C g p ∶ apply C p zero
    +F : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ +F A B ∶ 𝒰 ℓ
    +IL : ∀ {ℓ A a B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ +IL a ∶ +F A B
    +IR : ∀ {ℓ A B b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ b ∶ B →
      Γ ⊢ +IR b ∶ +F A B
    +E : ∀ {ℓ A B C c d e} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (weaken C) (+IL (𝓋 zero)) (suc zero) →
        suc Γ ⊢ d ∶ apply (weaken C) (+IR (𝓋 zero)) (suc zero) →
        Γ ⊢ e ∶ +F A B →
      Γ ⊢ +E C c d e ∶ apply C e zero
    𝟘F : ∀ {ℓ} →
      Γ ⊢ 𝟘F ∶ 𝒰 ℓ
    𝟘E : ∀ {ℓ C a} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ a ∶ 𝟘F →
      Γ ⊢ 𝟘E C a ∶ apply C a zero
-}
    𝟙F : ∀ {ℓ} →
      Γ ⊢ 𝟙F ∶ 𝒰 ℓ
    𝟙I :
      Γ ⊢ 𝟙I ∶ 𝟙F
    𝟙E : ∀ {ℓ C c a} →
      Γ ,, (𝟙F {ℓ = ℓ}) ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c ∶ apply C 𝟙I zero → Γ ⊢ a ∶ 𝟙F →
      Γ ⊢ 𝟙E C c a ∶ apply C a zero
{-
    ℕF : ∀ {ℓ} →
      Γ ⊢ ℕF ∶ 𝒰 ℓ
    ℕIZ :
      Γ ⊢ ℕIZ ∶ ℕF
    ℕIS : ∀ {n} →
      Γ ⊢ n ∶ ℕF →
      Γ ⊢ ℕIS n ∶ ℕF
    ℕE : ∀ {ℓ C c₀ cₛ n} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c₀ ∶ apply C ℕIZ zero → suc (suc Γ) ⊢ cₛ ∶ weaken (apply (weaken C) (ℕIS (𝓋 zero)) (suc zero)) →
      Γ ⊢ ℕE C c₀ cₛ n ∶ apply C n zero
    =F : ∀ {ℓ A a b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ A →
      Γ ⊢ =F A a b ∶ 𝒰 ℓ
    =I : ∀ {ℓ A a} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ =I a ∶ =F A a a
    =E : ∀ {ℓ C c A a b p} →
        suc (suc (suc Γ)) ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (apply (apply (weaken C) (=I (𝓋 zero)) (suc zero))
                                 (𝓋 zero) (suc zero))
                          (𝓋 zero) (suc zero) →
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ A →
        Γ ⊢ p ∶ =F A a b →
        Γ ⊢ =E C c a b p ∶ apply (apply (apply C (weaken (weaken p)) zero) (weaken b) zero) a zero

-}

    Vble :
      ∀ n A →
      Γ at n ≡ A →
      Γ ⊢ 𝓋 n ∶ A
  module TestYourJudgement where
    test : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (weaken 𝟙F)
    test = ΠI (𝟙F {ℓ = zero}) (Vble zero (([] ,, (𝟙F {ℓ = zero})) at zero) refl)

    test' : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (ΠI 𝟙F)
    test' = ΠI (𝟙F {ℓ = zero}) (Vble zero (ΠI 𝟙F) {!!})
```

That sorta works also. But it's time to take weakness seriously.

I wonder if there's a way (without a macro) to write `weaken` without a bunch of cases. Let's try a simplified example.

```agda
module TakingWeakenSeriously′1 where

  open Preliminary

  Universe = Nat

  data Term (N : Nat) : Set where
    𝒰 : Universe → Term N
    𝓋 : Fin N → Term N
    ΠF : Term N → Term (suc N) → Term N
    ΠI : Term (suc N) → Term N

  weakenFinFrom : ∀ {N} → Fin N → Fin N → Fin (suc N)
  weakenFinFrom x zero = suc x
  weakenFinFrom zero (suc from) = zero
  weakenFinFrom (suc x) (suc from) = suc (weakenFinFrom x from)

  weakenTermFrom : ∀ {N} → Term N → Fin N → Term (suc N)
  weakenTermFrom (𝒰 ℓ) from = 𝒰 ℓ
  weakenTermFrom (𝓋 x) from = 𝓋 (weakenFinFrom x from)
  weakenTermFrom (ΠF t₁ t₂) from = ΠF (weakenTermFrom t₁ from) (weakenTermFrom t₂ (suc from))
  weakenTermFrom (ΠI t₁) from = ΠI (weakenTermFrom t₁ (suc from))
```

The nice part is that, except for getting the constructors on the rhs correct, and ordering the terms given, it's very hard to screw this up. For example, not applying the correct amount of `suc`s to `from` causes a type-check error.

Let's consider how I might write a more generic version without a macro.

```agda
  data PrimitiveConstant : List Nat → Set where
    ΠF : PrimitiveConstant (0 ∷ 1 ∷ [])
    ΠI : PrimitiveConstant (1 ∷ [])

  wk⟦_⟧ : (A : Nat → Set) → List Nat → ∀ {N} → A N → Fin N → A (suc N)
  wk⟦_⟧ = {!!}

```

I'm reminded of Conor McBride's Metaprogramming in Agda.

But before I get too meta, let me see that the rest of the plan will work out.

```agda
module A2TT′*4 where

  open Preliminary

  Universe = Nat
  Complexity = Nat

  data Term (N : Nat) : Set where
    𝒰 : Universe → Term N
    𝓋 : Fin N → Term N
    ΠF : Term N → Term (suc N) → Term N
    ΠI : Term (suc N) → Term N
    ΠE : Term N → Term N → Term N
    ΣF : Term N → Term (suc N) → Term N
    ΣI : Term N → Term N → Term N
    ΣE : Term (suc N) → Term (suc (suc N)) → Term N → Term N
    +F : Term N → Term N → Term N
    +IL : Term N → Term N
    +IR : Term N → Term N
    +E : Term (suc N) → Term (suc N) → Term (suc N) → Term N → Term N
    𝟘F : Term N
    𝟘E : Term (suc N) → Term N → Term N
    𝟙F : Term N
    𝟙I : Term N
    𝟙E : Term (suc N) → Term N → Term N → Term N
    ℕF : Term N
    ℕIZ : Term N
    ℕIS : Term N → Term N
    ℕE : Term (suc N) → Term N → Term (suc (suc N)) → Term N → Term N
    =F : Term N → Term N → Term N → Term N
    =I : Term N → Term N
    =E : Term (suc (suc (suc N))) → Term (suc N) → Term N → Term N → Term N → Term N

  weakenFinFrom : ∀ {N} → Fin N → Fin N → Fin (suc N)
  weakenFinFrom x zero = suc x
  weakenFinFrom zero (suc from) = zero
  weakenFinFrom (suc x) (suc from) = suc (weakenFinFrom x from)

  weakenTermFrom : ∀ {N} → Term N → Fin N → Term (suc N)
  weakenTermFrom (𝒰 x) from = (𝒰 x)
  weakenTermFrom (𝓋 x) from = 𝓋 (weakenFinFrom x from)
  weakenTermFrom (ΠF t₁ t₂) from = ΠF (weakenTermFrom t₁ from) (weakenTermFrom t₂ (suc from))
  weakenTermFrom (ΠI t₁) from = ΠI (weakenTermFrom t₁ (suc from))
  weakenTermFrom (ΠE t₁ t₂) from = ΠE (weakenTermFrom t₁ from) (weakenTermFrom t₂ from)
  weakenTermFrom (ΣF t₁ t₂) from = {!!}
  weakenTermFrom (ΣI t₁ t₂) from = {!!}
  weakenTermFrom (ΣE t₁ t₂ t₃) from = {!!}
  weakenTermFrom (+F t₁ t₂) from = {!!}
  weakenTermFrom (+IL t₁) from = {!!}
  weakenTermFrom (+IR t₁) from = {!!}
  weakenTermFrom (+E x x₁ x₂ x₃) from = {!!}
  weakenTermFrom 𝟘F from = 𝟘F
  weakenTermFrom (𝟘E x x₁) from = {!!}
  weakenTermFrom 𝟙F from = 𝟙F
  weakenTermFrom 𝟙I from = 𝟙I
  weakenTermFrom (𝟙E t₁ t₂ t₃) from = 𝟙E (weakenTermFrom t₁ (suc from)) (weakenTermFrom t₂ from) (weakenTermFrom t₃ from)
  weakenTermFrom ℕF from = {!!}
  weakenTermFrom ℕIZ from = {!!}
  weakenTermFrom (ℕIS x) from = {!!}
  weakenTermFrom (ℕE x x₁ x₂ x₃) from = {!!}
  weakenTermFrom (=F x x₁ x₂) from = {!!}
  weakenTermFrom (=I x) from = {!!}
  weakenTermFrom (=E x x₁ x₂ x₃ x₄) from = {!!}

  weaken : ∀ {N} → Term N → Term (suc N)
  weaken {zero} = {!weakenTermFrom!}
  weaken {suc N} = {!!} -- weakenTermFrom t zero

  apply : ∀ {N} → Term (suc N) → Term N → Fin (suc N) → Term N
  apply = {!!}

  data _ctx : Nat → Set
  data _⊢_∶_ {N : Nat} (Γ : N ctx) : Term N → Term N → Set

  infixl 25 _,,_
  data _ctx where
    [] : zero ctx
    _,,_ : ∀ {N ℓ A} → (Γ : N ctx) → Γ ⊢ A ∶ 𝒰 ℓ → suc N ctx

  _at_ : ∀ {N} → N ctx → Fin N → Term N
  _,,_ {A = A} Γ γ at zero = weaken A
  (Γ ,, _) at suc n = weaken (Γ at n)

  data _⊢_∶_ {N : Nat} (Γ : N ctx) where
    𝒰I : ∀ ℓ →
      Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
    𝒰C : ∀ {ℓ A} →
      Γ ⊢ A ∶ 𝒰 ℓ →
      Γ ⊢ A ∶ 𝒰 (suc ℓ)
    ΠF : ∀ {ℓ A B} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) → Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΠF A B ∶ 𝒰 ℓ
    ΠI : ∀ {ℓ A b B} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      Γ ,, ⊢A ⊢ b ∶ B →
      Γ ⊢ ΠI b ∶ ΠF A B
    ΠE : ∀ {f A a B} →
      Γ ⊢ f ∶ ΠF A B → Γ ⊢ a ∶ A →
      Γ ⊢ ΠE f a ∶ apply B a zero
{-
    ΣF : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → suc Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΣF A B ∶ 𝒰 ℓ
    ΣI : ∀ {ℓ A a B b} →
      suc Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ apply B a zero →
      Γ ⊢ ΣI a b ∶ ΣF A B
    ΣE : ∀ {ℓ A B C g p} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc (suc Γ) ⊢ g ∶ apply (weaken (weaken C)) (ΣI (𝓋 (suc zero)) (𝓋 zero)) (suc (suc zero)) →
        Γ ⊢ p ∶ ΣF A B →
      Γ ⊢ ΣE C g p ∶ apply C p zero
    +F : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ +F A B ∶ 𝒰 ℓ
    +IL : ∀ {ℓ A a B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ +IL a ∶ +F A B
    +IR : ∀ {ℓ A B b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ b ∶ B →
      Γ ⊢ +IR b ∶ +F A B
    +E : ∀ {ℓ A B C c d e} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (weaken C) (+IL (𝓋 zero)) (suc zero) →
        suc Γ ⊢ d ∶ apply (weaken C) (+IR (𝓋 zero)) (suc zero) →
        Γ ⊢ e ∶ +F A B →
      Γ ⊢ +E C c d e ∶ apply C e zero
    𝟘F : ∀ {ℓ} →
      Γ ⊢ 𝟘F ∶ 𝒰 ℓ
    𝟘E : ∀ {ℓ C a} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ a ∶ 𝟘F →
      Γ ⊢ 𝟘E C a ∶ apply C a zero
-}
    𝟙F : ∀ {ℓ} →
      Γ ⊢ 𝟙F ∶ 𝒰 ℓ
    𝟙I :
      Γ ⊢ 𝟙I ∶ 𝟙F
    𝟙E : ∀ {ℓ C c a} →
      Γ ,, (𝟙F {ℓ = ℓ}) ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c ∶ apply C 𝟙I zero → Γ ⊢ a ∶ 𝟙F →
      Γ ⊢ 𝟙E C c a ∶ apply C a zero
{-
    ℕF : ∀ {ℓ} →
      Γ ⊢ ℕF ∶ 𝒰 ℓ
    ℕIZ :
      Γ ⊢ ℕIZ ∶ ℕF
    ℕIS : ∀ {n} →
      Γ ⊢ n ∶ ℕF →
      Γ ⊢ ℕIS n ∶ ℕF
    ℕE : ∀ {ℓ C c₀ cₛ n} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c₀ ∶ apply C ℕIZ zero → suc (suc Γ) ⊢ cₛ ∶ weaken (apply (weaken C) (ℕIS (𝓋 zero)) (suc zero)) →
      Γ ⊢ ℕE C c₀ cₛ n ∶ apply C n zero
    =F : ∀ {ℓ A a b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ A →
      Γ ⊢ =F A a b ∶ 𝒰 ℓ
    =I : ∀ {ℓ A a} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ =I a ∶ =F A a a
    =E : ∀ {ℓ C c A a b p} →
        suc (suc (suc Γ)) ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (apply (apply (weaken C) (=I (𝓋 zero)) (suc zero))
                                 (𝓋 zero) (suc zero))
                          (𝓋 zero) (suc zero) →
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ A →
        Γ ⊢ p ∶ =F A a b →
        Γ ⊢ =E C c a b p ∶ apply (apply (apply C (weaken (weaken p)) zero) (weaken b) zero) a zero

-}

    Vble :
      ∀ n A →
      Γ at n ≡ A →
      Γ ⊢ 𝓋 n ∶ A
  module TestYourJudgement where
    test : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (weaken 𝟙F)
    test = ΠI (𝟙F {ℓ = zero}) (Vble zero (([] ,, (𝟙F {ℓ = zero})) at zero) refl)

    test' : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (ΠI 𝟙F)
    test' = ΠI (𝟙F {ℓ = zero}) (Vble zero (ΠI 𝟙F) {!!})
```

Actually, my weaken was wrong. I need to handle the case where the weakened argument gets placed at the bottom position.

```agda
module TakingWeakenSeriously′2 where

  open Preliminary

  Universe = Nat

  data Term (N : Nat) : Set where
    𝒰 : Universe → Term N
    𝓋 : Fin N → Term N
    ΠF : Term N → Term (suc N) → Term N
    ΠI : Term (suc N) → Term N

  weakenFinFrom : ∀ {N} → Fin (suc N) → Fin N → Fin (suc N)
  weakenFinFrom zero x = suc x
  weakenFinFrom (suc from) zero = zero
  weakenFinFrom (suc from) (suc x) = suc (weakenFinFrom from x)

  weakenTermFrom : ∀ {N} → Fin (suc N) → Term N → Term (suc N)
  weakenTermFrom from (𝒰 ℓ) = 𝒰 ℓ
  weakenTermFrom from (𝓋 x) = 𝓋 (weakenFinFrom from x)
  weakenTermFrom from (ΠF t₁ t₂) = ΠF (weakenTermFrom from t₁) (weakenTermFrom (suc from) t₂)
  weakenTermFrom from (ΠI t₁) = ΠI (weakenTermFrom (suc from) t₁)

  weakenTerm : ∀ {N} → Term N → Term (suc N)
  weakenTerm = weakenTermFrom zero
```

Now, let's try this again.

```agda
module A2TT′*5 where

  open Preliminary

  Universe = Nat
  Complexity = Nat

  data Term (N : Nat) : Set where
    𝒰 : Universe → Term N
    𝓋 : Fin N → Term N
    ΠF : Term N → Term (suc N) → Term N
    ΠI : Term (suc N) → Term N
    ΠE : Term N → Term N → Term N
    ΣF : Term N → Term (suc N) → Term N
    ΣI : Term N → Term N → Term N
    ΣE : Term (suc N) → Term (suc (suc N)) → Term N → Term N
    +F : Term N → Term N → Term N
    +IL : Term N → Term N
    +IR : Term N → Term N
    +E : Term (suc N) → Term (suc N) → Term (suc N) → Term N → Term N
    𝟘F : Term N
    𝟘E : Term (suc N) → Term N → Term N
    𝟙F : Term N
    𝟙I : Term N
    𝟙E : Term (suc N) → Term N → Term N → Term N
    ℕF : Term N
    ℕIZ : Term N
    ℕIS : Term N → Term N
    ℕE : Term (suc N) → Term N → Term (suc (suc N)) → Term N → Term N
    =F : Term N → Term N → Term N → Term N
    =I : Term N → Term N
    =E : Term (suc (suc (suc N))) → Term (suc N) → Term N → Term N → Term N → Term N

  weakenFinFrom : ∀ {N} → Fin (suc N) → Fin N → Fin (suc N)
  weakenFinFrom zero x = suc x
  weakenFinFrom (suc from) zero = zero
  weakenFinFrom (suc from) (suc x) = suc (weakenFinFrom from x)

  weakenTermFrom : ∀ {N} → Fin (suc N) → Term N → Term (suc N)
  weakenTermFrom from (𝒰 x) = (𝒰 x)
  weakenTermFrom from (𝓋 x) = 𝓋 (weakenFinFrom from x)
  weakenTermFrom from (ΠF t₁ t₂) = ΠF (weakenTermFrom from t₁) (weakenTermFrom (suc from) t₂)
  weakenTermFrom from (ΠI t₁) = ΠI (weakenTermFrom (suc from) t₁)
  weakenTermFrom from (ΠE t₁ t₂) = ΠE (weakenTermFrom from t₁) (weakenTermFrom from t₂)
  weakenTermFrom from (ΣF t₁ t₂) = ΣF (weakenTermFrom from t₁) (weakenTermFrom (suc from) t₂)
  weakenTermFrom from (ΣI t₁ t₂) = ΣI (weakenTermFrom from t₁) (weakenTermFrom from t₂)
  weakenTermFrom from (ΣE t₁ t₂ t₃) = ΣE (weakenTermFrom (suc from) t₁) (weakenTermFrom (suc (suc from)) t₂) (weakenTermFrom from t₃)
  weakenTermFrom from (+F t₁ t₂) = {!!}
  weakenTermFrom from (+IL t₁) = {!!}
  weakenTermFrom from (+IR t₁) = {!!}
  weakenTermFrom from (+E x x₁ x₂ x₃) = {!!}
  weakenTermFrom from 𝟘F = 𝟘F
  weakenTermFrom from (𝟘E t₁ t₂) = 𝟘E (weakenTermFrom (suc from) t₁) (weakenTermFrom from t₂)
  weakenTermFrom from 𝟙F = 𝟙F
  weakenTermFrom from 𝟙I = 𝟙I
  weakenTermFrom from (𝟙E t₁ t₂ t₃) = 𝟙E (weakenTermFrom (suc from) t₁) (weakenTermFrom from t₂) (weakenTermFrom from t₃)
  weakenTermFrom from ℕF = {!!}
  weakenTermFrom from ℕIZ = {!!}
  weakenTermFrom from (ℕIS x) = {!!}
  weakenTermFrom from (ℕE x x₁ x₂ x₃) = {!!}
  weakenTermFrom from (=F x x₁ x₂) = {!!}
  weakenTermFrom from (=I x) = {!!}
  weakenTermFrom from (=E x x₁ x₂ x₃ x₄) = {!!}

  weaken : ∀ {N} → Term N → Term (suc N)
  weaken = weakenTermFrom zero

  apply : ∀ {N} → Term (suc N) → Term N → Fin (suc N) → Term N
  apply = {!!}

  data _ctx : Nat → Set
  data _⊢_∶_ {N : Nat} (Γ : N ctx) : Term N → Term N → Set

  infixl 25 _,,_
  data _ctx where
    [] : zero ctx
    _,,_ : ∀ {N ℓ A} → (Γ : N ctx) → Γ ⊢ A ∶ 𝒰 ℓ → suc N ctx

  _at_ : ∀ {N} → N ctx → Fin N → Term N
  _,,_ {A = A} Γ γ at zero = weaken A
  (Γ ,, _) at suc n = weaken (Γ at n)

  data _⊢_∶_ {N : Nat} (Γ : N ctx) where
    𝒰I : ∀ ℓ →
      Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
    𝒰C : ∀ {ℓ A} →
      Γ ⊢ A ∶ 𝒰 ℓ →
      Γ ⊢ A ∶ 𝒰 (suc ℓ)
    ΠF : ∀ {ℓ A B} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) → Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΠF A B ∶ 𝒰 ℓ
    ΠI : ∀ {ℓ A b B} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      Γ ,, ⊢A ⊢ b ∶ B →
      Γ ⊢ ΠI b ∶ ΠF A B
    ΠE : ∀ {f A a B} →
      Γ ⊢ f ∶ ΠF A B → Γ ⊢ a ∶ A →
      Γ ⊢ ΠE f a ∶ apply B a zero
{-
    ΣF : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → suc Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ ΣF A B ∶ 𝒰 ℓ
    ΣI : ∀ {ℓ A a B b} →
      suc Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ apply B a zero →
      Γ ⊢ ΣI a b ∶ ΣF A B
    ΣE : ∀ {ℓ A B C g p} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc (suc Γ) ⊢ g ∶ apply (weaken (weaken C)) (ΣI (𝓋 (suc zero)) (𝓋 zero)) (suc (suc zero)) →
        Γ ⊢ p ∶ ΣF A B →
      Γ ⊢ ΣE C g p ∶ apply C p zero
    +F : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ →
      Γ ⊢ +F A B ∶ 𝒰 ℓ
    +IL : ∀ {ℓ A a B} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ +IL a ∶ +F A B
    +IR : ∀ {ℓ A B b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ B ∶ 𝒰 ℓ → Γ ⊢ b ∶ B →
      Γ ⊢ +IR b ∶ +F A B
    +E : ∀ {ℓ A B C c d e} →
        suc Γ ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (weaken C) (+IL (𝓋 zero)) (suc zero) →
        suc Γ ⊢ d ∶ apply (weaken C) (+IR (𝓋 zero)) (suc zero) →
        Γ ⊢ e ∶ +F A B →
      Γ ⊢ +E C c d e ∶ apply C e zero
    𝟘F : ∀ {ℓ} →
      Γ ⊢ 𝟘F ∶ 𝒰 ℓ
    𝟘E : ∀ {ℓ C a} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ a ∶ 𝟘F →
      Γ ⊢ 𝟘E C a ∶ apply C a zero
-}
    𝟙F : ∀ {ℓ} →
      Γ ⊢ 𝟙F ∶ 𝒰 ℓ
    𝟙I :
      Γ ⊢ 𝟙I ∶ 𝟙F
    𝟙E : ∀ {ℓ C c a} →
      Γ ,, (𝟙F {ℓ = ℓ}) ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c ∶ apply C 𝟙I zero → Γ ⊢ a ∶ 𝟙F →
      Γ ⊢ 𝟙E C c a ∶ apply C a zero
{-
    ℕF : ∀ {ℓ} →
      Γ ⊢ ℕF ∶ 𝒰 ℓ
    ℕIZ :
      Γ ⊢ ℕIZ ∶ ℕF
    ℕIS : ∀ {n} →
      Γ ⊢ n ∶ ℕF →
      Γ ⊢ ℕIS n ∶ ℕF
    ℕE : ∀ {ℓ C c₀ cₛ n} →
      suc Γ ⊢ C ∶ 𝒰 ℓ → Γ ⊢ c₀ ∶ apply C ℕIZ zero → suc (suc Γ) ⊢ cₛ ∶ weaken (apply (weaken C) (ℕIS (𝓋 zero)) (suc zero)) →
      Γ ⊢ ℕE C c₀ cₛ n ∶ apply C n zero
    =F : ∀ {ℓ A a b} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A → Γ ⊢ b ∶ A →
      Γ ⊢ =F A a b ∶ 𝒰 ℓ
    =I : ∀ {ℓ A a} →
      Γ ⊢ A ∶ 𝒰 ℓ → Γ ⊢ a ∶ A →
      Γ ⊢ =I a ∶ =F A a a
    =E : ∀ {ℓ C c A a b p} →
        suc (suc (suc Γ)) ⊢ C ∶ 𝒰 ℓ →
        suc Γ ⊢ c ∶ apply (apply (apply (weaken C) (=I (𝓋 zero)) (suc zero))
                                 (𝓋 zero) (suc zero))
                          (𝓋 zero) (suc zero) →
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ A →
        Γ ⊢ p ∶ =F A a b →
        Γ ⊢ =E C c a b p ∶ apply (apply (apply C (weaken (weaken p)) zero) (weaken b) zero) a zero

-}

    Vble :
      ∀ n A →
      Γ at n ≡ A →
      Γ ⊢ 𝓋 n ∶ A
  module TestYourJudgement where
    test : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (weaken 𝟙F)
    test = ΠI (𝟙F {ℓ = zero}) (Vble zero (([] ,, (𝟙F {ℓ = zero})) at zero) refl)

    test'' : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F (weaken 𝟙F)
    test'' = ΠI (𝟙F {ℓ = zero}) (Vble zero 𝟙F refl)

    test' : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F
    test' = ΠI (𝟙F {ℓ = zero}) (Vble zero 𝟙F refl)

    not-well-formed-1 : [] ⊢ 𝒰 zero ∶ ΠF 𝟙F 𝟙F → ⊥
    not-well-formed-1 ()
```

Looking good. Now let's show that typechecking is decidable.

******************************
** NB I have commented out the code block below to save type-checking time
*******************************
```agda
{-
  TC-decidable' : ∀ {N} (Γ : N ctx) (a : Term N) (A : Term N) → ¬ ¬ Γ ⊢ a ∶ A → Γ ⊢ a ∶ A
  TC-decidable' Γ (𝒰 x₂) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (𝓋 x₂) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (ΠF a a₁) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (ΠI a) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (ΠE a a₁) (𝒰 x₁) x = {!!}
  TC-decidable' [] (ΣF a a₁) (𝒰 x₁) x = ⊥-elim (x λ { (𝒰C x₂) → {!!}})
  TC-decidable' (Γ ,, x₂) (ΣF a a₁) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (ΣI a a₁) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (ΣE a a₁ a₂) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (+F a a₁) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (+IL a) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (+IR a) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (+E a a₁ a₂ a₃) (𝒰 x₁) x = {!!}
  TC-decidable' Γ 𝟘F (𝒰 x₁) x = {!!}
  TC-decidable' Γ (𝟘E a a₁) (𝒰 x₁) x = {!!}
  TC-decidable' Γ 𝟙F (𝒰 x₁) x = {!!}
  TC-decidable' Γ 𝟙I (𝒰 x₁) x = {!!}
  TC-decidable' Γ (𝟙E a a₁ a₂) (𝒰 x₁) x = {!!}
  TC-decidable' Γ ℕF (𝒰 x₁) x = {!!}
  TC-decidable' Γ ℕIZ (𝒰 x₁) x = {!!}
  TC-decidable' Γ (ℕIS a) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (ℕE a a₁ a₂ a₃) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (=F a a₁ a₂) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (=I a) (𝒰 x₁) x = {!!}
  TC-decidable' Γ (=E a a₁ a₂ a₃ a₄) (𝒰 x₁) x = {!!}
  TC-decidable' Γ a (𝓋 x₁) x = {!!}
  TC-decidable' Γ (𝒰 x₁) (ΠF A A₁) x = ⊥-elim (x λ { ()})
  TC-decidable' Γ (𝓋 x₁) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ΠF a a₁) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ΠI a) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ΠE a a₁) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ΣF a a₁) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ΣI a a₁) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ΣE a a₁ a₂) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (+F a a₁) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (+IL a) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (+IR a) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (+E a a₁ a₂ a₃) (ΠF A A₁) x = {!!}
  TC-decidable' Γ 𝟘F (ΠF A A₁) x = {!!}
  TC-decidable' Γ (𝟘E a a₁) (ΠF A A₁) x = {!!}
  TC-decidable' Γ 𝟙F (ΠF A A₁) x = {!!}
  TC-decidable' Γ 𝟙I (ΠF A A₁) x = {!!}
  TC-decidable' Γ (𝟙E a a₁ a₂) (ΠF A A₁) x = {!!}
  TC-decidable' Γ ℕF (ΠF A A₁) x = {!!}
  TC-decidable' Γ ℕIZ (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ℕIS a) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (ℕE a a₁ a₂ a₃) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (=F a a₁ a₂) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (=I a) (ΠF A A₁) x = {!!}
  TC-decidable' Γ (=E a a₁ a₂ a₃ a₄) (ΠF A A₁) x = {!!}
  TC-decidable' Γ a (ΠI A) x = {!!}
  TC-decidable' Γ a (ΠE A A₁) x = {!!}
  TC-decidable' Γ a (ΣF A A₁) x = {!!}
  TC-decidable' Γ a (ΣI A A₁) x = {!!}
  TC-decidable' Γ a (ΣE A A₁ A₂) x = {!!}
  TC-decidable' Γ a (+F A A₁) x = {!!}
  TC-decidable' Γ a (+IL A) x = {!!}
  TC-decidable' Γ a (+IR A) x = {!!}
  TC-decidable' Γ a (+E A A₁ A₂ A₃) x = {!!}
  TC-decidable' Γ a 𝟘F x = {!!}
  TC-decidable' Γ a (𝟘E A A₁) x = {!!}
  TC-decidable' Γ a 𝟙F x = {!!}
  TC-decidable' Γ a 𝟙I x = {!!}
  TC-decidable' Γ a (𝟙E A A₁ A₂) x = {!!}
  TC-decidable' Γ a ℕF x = {!!}
  TC-decidable' Γ a ℕIZ x = {!!}
  TC-decidable' Γ a (ℕIS A) x = {!!}
  TC-decidable' Γ a (ℕE A A₁ A₂ A₃) x = {!!}
  TC-decidable' Γ a (=F A A₁ A₂) x = {!!}
  TC-decidable' Γ a (=I A) x = {!!}
  TC-decidable' Γ a (=E A A₁ A₂ A₃ A₄) x = {!!}

  TC-decidable : ∀ {N} (Γ : N ctx) (a : Term N) (A : Term N) → Dec (Γ ⊢ a ∶ A)
  TC-decidable Γ (𝒰 x) (𝒰 x₁) = {!!}
  TC-decidable Γ (𝒰 x) (𝓋 x₁) = no λ { ()}
  TC-decidable Γ (𝒰 x) (ΠF A A₁) = {!!}
  TC-decidable Γ (𝒰 x) (ΠI A) = {!!}
  TC-decidable Γ (𝒰 x) (ΠE A A₁) = {!!}
  TC-decidable Γ (𝒰 x) (ΣF A A₁) = {!!}
  TC-decidable Γ (𝒰 x) (ΣI A A₁) = {!!}
  TC-decidable Γ (𝒰 x) (ΣE A A₁ A₂) = {!!}
  TC-decidable Γ (𝒰 x) (+F A A₁) = {!!}
  TC-decidable Γ (𝒰 x) (+IL A) = {!!}
  TC-decidable Γ (𝒰 x) (+IR A) = {!!}
  TC-decidable Γ (𝒰 x) (+E A A₁ A₂ A₃) = {!!}
  TC-decidable Γ (𝒰 x) 𝟘F = {!!}
  TC-decidable Γ (𝒰 x) (𝟘E A A₁) = {!!}
  TC-decidable Γ (𝒰 x) 𝟙F = {!!}
  TC-decidable Γ (𝒰 x) 𝟙I = {!!}
  TC-decidable Γ (𝒰 x) (𝟙E A A₁ A₂) = {!!}
  TC-decidable Γ (𝒰 x) ℕF = {!!}
  TC-decidable Γ (𝒰 x) ℕIZ = {!!}
  TC-decidable Γ (𝒰 x) (ℕIS A) = {!!}
  TC-decidable Γ (𝒰 x) (ℕE A A₁ A₂ A₃) = {!!}
  TC-decidable Γ (𝒰 x) (=F A A₁ A₂) = {!!}
  TC-decidable Γ (𝒰 x) (=I A) = {!!}
  TC-decidable Γ (𝒰 x) (=E A A₁ A₂ A₃ A₄) = {!!}
  TC-decidable Γ (𝓋 x) A = {!!}
  TC-decidable Γ (ΠF a a₁) A = {!!}
  TC-decidable Γ (ΠI a) A = {!!}
  TC-decidable Γ (ΠE a a₁) A = {!!}
  TC-decidable Γ (ΣF a a₁) A = {!!}
  TC-decidable Γ (ΣI a a₁) A = {!!}
  TC-decidable Γ (ΣE a a₁ a₂) A = {!!}
  TC-decidable Γ (+F a a₁) A = {!!}
  TC-decidable Γ (+IL a) A = {!!}
  TC-decidable Γ (+IR a) A = {!!}
  TC-decidable Γ (+E a a₁ a₂ a₃) A = {!!}
  TC-decidable Γ 𝟘F A = {!!}
  TC-decidable Γ (𝟘E a a₁) A = {!!}
  TC-decidable Γ 𝟙F A = {!!}
  TC-decidable Γ 𝟙I A = {!!}
  TC-decidable Γ (𝟙E a a₁ a₂) A = {!!}
  TC-decidable Γ ℕF A = {!!}
  TC-decidable Γ ℕIZ A = {!!}
  TC-decidable Γ (ℕIS a) A = {!!}
  TC-decidable Γ (ℕE a a₁ a₂ a₃) A = {!!}
  TC-decidable Γ (=F a a₁ a₂) A = {!!}
  TC-decidable Γ (=I a) A = {!!}
  TC-decidable Γ (=E a a₁ a₂ a₃ a₄) A = {!!}
-}
```

Well, we can't quite do that yet until we've finished the definitions. But the above shows a good POC that it will work.

Recall that I had previously said:

    for a made-to-order proof theory (say, what I imagine developing with a la Natural Deduction), what I want is this:
      decidable : ∀ {ℓ} (τ : Type [] ℓ) n → ¬ ¬ FinTerm τ n → FinTerm τ n
      complete : ∀ {ℓ} (τ : Type [] ℓ) → Term τ → ∃ λ n → FinTerm τ n
      consistent : ¬ ∃ λ n → FinTerm 𝟘 n
      sound : ∀ {ℓ} (τ : Type [] ℓ) n → FinTerm τ n → Term τ
    What I will never get is this:
      magic₁ : ∀ {ℓ} (τ : Type [] ℓ) → ¬ ¬ ∃ λ n → FinTerm τ n → ∃ λ n → FinTerm τ n
    or even this:
      magic₂ : ∀ {ℓ} (τ : Type [] ℓ) → ¬ (∀ n → ¬ FinTerm τ n) → ∃ λ n → FinTerm τ n

In this case, FinTerm {Γ} A χ means that a procedure to determine whether there is an a such that Γ ⊢ a ∶ A completes in χ time. Or something like that. I believe that Term {Γ} A meant exactly ∃ λ a → Γ ⊢ a ∶ A. I will define this as ⊨ and will reserve ⊩ for FinTerm.

Actually, we need three arguments for that, so let's just call it TP (for theorem prover). Or maybe wait till I figure out more.

```agda
  _⊨_ : ∀ {N} → (Γ : N ctx) → Term N → Set
  Γ ⊨ A = ∃ λ a → Γ ⊢ a ∶ A

  data TP : ∀ {N} → (Γ : N ctx) (A : Term N) → Complexity → Set where
```

Now we can try to prove consistency.

```agda
  consistent : ¬ [] ⊨ 𝟘F
  consistent (𝒰 x , ())
  consistent (𝓋 () , snd₁)
  consistent (ΠF fst₁ fst₂ , ())
  consistent (ΠI fst₁ , snd₁) = {!!}
  consistent (ΠE fst₁ fst₂ , snd₁) = {!!}
  consistent (ΣF fst₁ fst₂ , snd₁) = {!!}
  consistent (ΣI fst₁ fst₂ , snd₁) = {!!}
  consistent (ΣE fst₁ fst₂ fst₃ , snd₁) = {!!}
  consistent (+F fst₁ fst₂ , snd₁) = {!!}
  consistent (+IL fst₁ , ())
  consistent (+IR fst₁ , snd₁) = {!!}
  consistent (+E fst₁ fst₂ fst₃ fst₄ , snd₁) = {!!}
  consistent (𝟘F , ())
  consistent (𝟘E fst₁ fst₂ , ())
  consistent (𝟙F , snd₁) = {!!}
  consistent (𝟙I , snd₁) = {!!}
  consistent (𝟙E fst₁ fst₂ fst₃ , snd₁) = {!!}
  consistent (ℕF , snd₁) = {!!}
  consistent (ℕIZ , snd₁) = {!!}
  consistent (ℕIS fst₁ , snd₁) = {!!}
  consistent (ℕE fst₁ fst₂ fst₃ fst₄ , snd₁) = {!!}
  consistent (=F fst₁ fst₂ fst₃ , ())
  consistent (=I fst₁ , ())
  consistent (=E fst₁ fst₂ fst₃ fst₄ fst₅ , snd₁) = {!!}
```

That feels too easy. Probably maybe because I haven't put in a lot of the data structure for _⊢_∶_. But let's press on anyway.

I think that to get TP, I should simply redefine the type checker:

```agda
  data _ctx≤_ : Nat → Complexity → Set
  data _⊩_∶_≤_ {N χ} (Γ : N ctx≤ χ) : Term N → Term N → Complexity → Set

  data _ctx≤_ where
    [] : zero ctx≤ zero
    _,,_ : ∀ {N ℓ A χ δ} → (Γ : N ctx≤ χ) → Γ ⊩ A ∶ 𝒰 ℓ ≤ δ → suc N ctx≤ max χ δ

  -- this is just a sample
  data _⊩_∶_≤_ {N χ} (Γ : N ctx≤ χ) where
    𝒰I : ∀ ℓ →
      Γ ⊩ 𝒰 ℓ ∶ 𝒰 (suc ℓ) ≤ zero
    𝒰C : ∀ {ℓ A χ} →
      Γ ⊩ A ∶ 𝒰 ℓ ≤ χ →
      Γ ⊩ A ∶ 𝒰 (suc ℓ) ≤ suc χ
    ΠF : ∀ {ℓ A B} →
      (⊩A : Γ ⊩ A ∶ 𝒰 ℓ ≤ {!!}) → Γ ,, ⊩A ⊩ B ∶ 𝒰 ℓ ≤ {!!} →
      Γ ⊩ ΠF A B ∶ 𝒰 ℓ ≤ {!!}
    ΠI : ∀ {ℓ A b B} →
      (⊩A : Γ ⊩ A ∶ 𝒰 ℓ ≤ {!!}) →
      Γ ,, ⊩A ⊩ b ∶ B ≤ {!!} →
      Γ ⊩ ΠI b ∶ ΠF A B ≤ {!!}
    ΠE : ∀ {f A a B} →
      Γ ⊩ f ∶ ΠF A B ≤ {!!} → Γ ⊩ a ∶ A ≤ {!!} →
      Γ ⊩ ΠE f a ∶ apply B a zero ≤ {!!}
```

Actually, we want space as well as time complexity. Inference to 𝒰I may be considered to take zero time (or should it be suc zero?), but what about the fact of ℓ? If it's large, that might matter. So, there are many issues here. Whether to use `max` in the context extension, the fact that we need to take `apply` and even `weaken` into account, etc.

I think the complexity should be the number of branches (premises) added to the maximum of the complexities of the branches.

Continued in YAF11.lagda.md (ramblings about meta programming)

Also continued in TypeTheory-2.lagda.md
