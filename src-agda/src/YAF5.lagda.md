
# Wherein I think I am building the architecture for a type theory proof system

```agda
module YAF5 where
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
```

## Introductory <strikeout>ramblings</strikeout> remarks

It is possible that this is inspired by Robert Harper's notion of the Holy Trinity: Logic, Languages, and Categories. (Although I don't quite yet get the Categories part, so it's probably not so proper to have said that.)

More to the point of what's on my mind: in building an automated proof system, some fundamental questions of adequacy arise, chief among them for me is, "does the automated proof system prove anything that is provable from the inference rules?" This is a question of the _completeness_ of the _automaton_, which is separate from the question of the completeness of the _calculus_. The former is measured with respect to the calculus, while the latter is measured with respect to the semantics. I would like to build a proof system in as general a form as I can muster, while addressing these and other questions of adequacy.

I conjecture that I can build a system for intuitionistic predicate logic and prove some worthy things about it. However, this will take quite a lot of work, and it's possible that what I end up with will be so vastly different from what I expected that I'll be sorry later. Probably that means I should get straight to work, but, nevertheless, I would like instead to consider rather a framework for building such a system.

So what are the essential elements?

"Logic." There are the judgements we would like to make. In the case of classical predicate logic, the main judgement is whether a given proposition is tautologous or contradictory. In the case of intuitionistic type theory, the main judgements concern the inhabitation of types and equality between terms. In the case of (John L. Pollock's) probability theory, the judgements may concern expectable values relative to a pair of n-place properties. In all of these cases there may yet be more judgements, such as whether a given linguistic element is well-formed.

"Structure." In each of these cases, we will want a theory describing conditions under which the judgements should or should not hold. In the case of classical predicate logic, typically we have a notion of a model, of truth of a proposition as interpreted in the the model, and we ask whether the proposition is true across all models. [TODO: add other cases; also the preceeding is probably horribly wrong]

"Language." There has to be something material that gets fed into the system and something that gets produced by it. In the case of classical predicate logic, we give the system a sequence of symbols and, on a good day, out comes a deductive proof. In the case of intuitionistic predicate logic, that proof is itself regarded as a program.

That is probably enough dilly-dallying for now. Let's now build a full-fledged automated proof system for intuitionistic predicate logic. Afterwards, we can think about generalising certain notions and then build the One True Program.

I may have gotten ahead of myself.

The Curry-Howard isomorphism relates proofs of propositions to elements of sets and to points of space. John L. Pollock distinguishes between propositions (objects of belief) and statements (products of assertion). One might conjecture that propositions (in Pollock's sense) are usefully to be identified with types and statements with terms. However, an objection to this is that this would make propositions coarse-grained statements (since every term can be identified with some type and every type can be identified with a set of terms).

The toughest part about programming the logic involves substitution, which itself is used in the elimination and computation rules. On equal footing (??) is matching (also called unification). It is tedious to spell these out for each given language, so it would be nice to simply talk about the necessary properties thereof.

Gödel incompleteness is a feature (defect?) of languages with a certain expressive ability. Perhaps instead of designing a language from the ground up (alphabet, rules of formation, etc.), we could ask what characteristics a language needs to have to express a Gödel sentence. The nice thing about this approach is that it invokes certain salient features that we already know we want in a proof system: negation, quantification, proof verification, and variable substitution. We may in fact get more than we were asking for (which may or may not help us/me): self-reference.

I take it that quotation marks provide a way of mentioning a linguistic element (a sentence, word, punctuation mark, or letter) without using it. For example, 'dog' is a three letter word, not a kind of animal, but a dog is a kind of animal, not a three-letter word.

It seems that there is no way to avoid self-reference when it comes to thinking about one's own beliefs. That may be tautologous, but it is profound nevertheless (that's just my opinion). For example, I may have a belief about John. The belief itself situates John in relation to me. But how about my assertions about John? If I say, "John wrote a book", the statement itself presumably does not involve self-reference. On the other hand, a statement such as that designated by "This sentence is false" is clearly self-referential. What about a sentence such as, "for proofs, see the appendix" appearing in John's book? The statement makes reference to the appendix of the book in which the sentence appears, and so is (perhaps indirectly?) self-referential. Even terms like "for example" are sneakily self-referential, for they direct the hearer to consider the following statement as an exemplar of the previous one. One could have written instead of "for example", "the following statement serves as an example of the previous statement (to this one)".

I hope to clear-up what is (or was) to me a mystery about Gödel's incompleteness theorem: how does he manage to construct a formal sentence that refers to itself? Especially when the language he uses allows for such a dearth of expression. I aim to show how to rewrite the mysterious sentence in a meta-language.


>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> these are scribbles
>>
>> I take it also that there are words
>>
>> (D) The x ate my homework.
>>
>> (D*) The sentence formed by concatenation of the sentential tokens the capitalization of 'the', 'dog', 'ate', 'my', 'homework', is true.
>>
>> (D**) D is true.
>>
>> (D***) ⌜The dog ate my homework.⌝
>>
>> The sentence formed by concatenation of the words 'the', 'sentence', 'formed', ..., 'words', the quotation of 'the', the quotation of 'dog', ... 'the', 'dog', 'ate', 'my', and 'homework' is true.
>>
>> Let's try to demonstrate Gödel incompleteness in (more-or-less) plain language. In this less-than-plain language, I will assume that we can talk about sentences and sentence forms. All sentences are sentence forms, but some sentence forms have free variables in places where sub-sentences (prepositional phrases?) might go. I will assume that we could take any sentence form, and by substituting any sentence in place of the free variables, we would obtain a sentence. I will use Quinean quotes ⌜⌝ to ...
>>
>> I will take it that the term 'proof' (and cognates)
>>
>> The Gödel sentence says "this sentence is unprovable". More precisely, let 'Φ' be a sentential form designator of sentential forms indexed by the free variable 'φ' over the class of sentential forms and written thusly:
>>
>> (Φ) It is not the case that there exists a proof of the sentence formed by substituting the free variable designated by 'φ' for ⌜the sentential form designator of φ⌝ within the sentential form ⌜φ⌝.
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

>> What is a schema? What is it to contain free variables? etc. etc.





>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
>> ``agda
>> module ZeroTrueProgram where
>>
>>   data Judgement (Value : Set) (Type : Set) : Set where
>>
>>
>>   data Formula :
>>     existence :
>>
>>   -- A `Proposition` is indexed by the number of free variables. Perhaps this should be called a "propositional schema".
>>   data Proposition : Nat → Set where
>>     variable : ∀ {n} → Fin (suc n) → Proposition (suc n)
>>     universe : Nat → Proposition 0
>>     application : ∀ {n} → Proposition n → Proposition n → Proposition n
>>     abstraction : ∀ {n} → Proposition n → Proposition (suc n) → Proposition n
>>     constructor : ∀ {n N} → Nat → Vec (Proposition n) N → Proposition n
>>     function :
>>
>>     application : Proposition
>>     Pi :
>>     𝟎 : Proposition
>>     substitute : ∀ {m n N} →
>>                  m ≤ n →
>>                  N ≡ m - n →
>>                  Proposition n →
>>                  Vec (Proposition m) N →
>>                  Proposition m
>>
>>   -- a `Context` is indexed by the number of propositions contained therein. Free variables in
>>   data Context : Nat → Set
>>     [] : Context 0
>>     _∷_ : ∀ {n} → Proposition n → Context n → Context (suc n)
>>
>>
>>   data Assumption : Set where
>>
>>
>>   data Judgement : Set where
>>     ctx :
>>
>>   data Derivation : Judgement → Set where
>>
>>
>>   data
>>
>>
>>   data
>>
>>
>>   data Judgement : Set where
>>     _ctx : Context → Judgement
>>     _⊢_⦂_  : Context → Term → Type → Judgement
>>     _⊢_≡_⦂_ : Context → Term → Term → Type → Judgement
>>
>>   data Context : Set
>>   data Proposition : Set
>>   data Proof : Set
>>   data Derivation : Set
>>
>>
>>
>> -}
>>
>> {-
>>   record InferenceRule (Judgement : Set) : Set where
>>     field
>>       premises : {n : Nat} → Vec Judgement (suc n)
>>       conclusion : Judgement
>> -}
>> {-
>>   record ProofSystem : Set where
>>     field
>> -}
>> ``
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

Let's try this again.

I would like to create a proof system capable of deriving a constructive proof of (GCD) the existence of a greatest common denominator (for any two natural numbers, not both zero).

Let's construct a proof of GCD first in Agda. I want to be sure that I know what sorts of types will be needed (e.g. I'm not sure if I need a separate type for ≤ or if I can get away with using more generic types.

```agda
module AgdaGCD where
  open Preliminary
    using (Nat; suc; zero; _≡_; refl; Σ; _,_; ∃_; _×_; fst; snd; left; right; ⊥; ⊥-elim)
    renaming (Either to _∨_)
  -- open import Prelude.Number

  indNat : (C : Nat → Set) → C zero → ((n : Nat) → C n → C (suc n)) → ∀ n → C n
  indNat _ c0 _ zero = c0
  indNat C c0 cs (suc n) = cs n (indNat C c0 cs n)

  indId : (A : Set) (C : (x y : A) → x ≡ y → Set) → (∀ z → C z z refl) → (a b : A) (p : a ≡ b) → C a b p
  indId A C c a .a refl = c a

  _+_ : Nat → Nat → Nat
  _+_ = indNat (λ _ → Nat → Nat)
               (λ n → n)
               (λ _ f n → suc (f n))

  _*_ : Nat → Nat → Nat
  _*_ = indNat (λ _ → Nat → Nat)
               (λ _ → zero)
               (λ _ f n → n + f n)

  left-id-+ : ∀ n → zero + n ≡ n
  left-id-+ = λ n → refl

  right-id-+n : ∀ n → n + zero ≡ n
  right-id-+n =
    λ n → indNat (λ n → indNat (λ _ → Nat → Nat) (λ n₁ → n₁) (λ _ f n₁ → suc (f n₁))
      n 0
      ≡ n) refl (λ n' → λ p → let g = λ n' → Nat.suc
                                        (indNat (λ _ → Nat → Nat) (λ n₁ → n₁) (λ _ f n₁ → suc (f n₁)) n' 0)
                                          ≡ suc n' in indNat g {!!} (λ n'' → λ p' → {!!}) n') n
    -- indNat _ refl λ n → indId Nat (λ x y _ → suc x ≡ suc y) (λ _ → refl) _ n

  test : 3 + 2 ≡ 5
  test = refl

  commutative-+n : ∀ m n → n + m ≡ m + n
  commutative-+n = λ m n → {!!} -- indId Nat (λ x y p → (x +n y) ≡ (y +n x)) (λ z → refl) n m {!!}

  _∣_ : Nat → Nat → Set
  _∣_ a b = ∃ λ n → b ≡ a * n

  _∈CD[_,_] : Nat → Nat → Nat → Set
  cd ∈CD[ a , b ] = cd ∣ a × cd ∣ b

  _<_ : Nat → Nat → Set
  _<_ a b = ∃ λ k → b ≡ suc k + a

  _≤_ : Nat → Nat → Set
  a ≤ b = (a ≡ b) ∨ (a < b)

  _≡GCD[_,_] : Nat → Nat → Nat → Set
  gcd ≡GCD[ a , b ] = gcd ∈CD[ a , b ] × ∀ cd → cd ∈CD[ a , b ] → (cd ≡ gcd) ∨ (cd < gcd)

  GCD : (a b : Nat) → (zero < a) ∨ (zero < b) → ∃ _≡GCD[ a , b ]
  GCD = λ a b 0<a∨0<b → zero , (({!!} , {!!}) , {!!} , {!!}) , λ cd cd∈a,b → {!!}

  absurdNat : (z : Nat) → suc z ≡ z
  absurdNat = {!!}

  not-all-0 : (∀ (n : Nat) → n ≡ zero) → ⊥
  not-all-0 = λ f → indId Nat (λ x y p → suc x ≡ y → ⊥) (λ z → {!!}) 0 zero refl (f (suc zero))

  gcd : (a b : Nat) → (a ≡ zero × b ≡ zero) ∨ (∃ _≡GCD[ a , b ])
  gcd = {!!}
  -- gcd (suc a) (suc b) = right (fst (GCD (suc a) (suc b) (left (a , indNat (λ (n : Nat) → Nat.suc n ≡ suc (n +N 0)) (refl , λ n x → indId Nat (λ x y p → Nat.suc x ≡ suc y) (λ z → refl) (suc n) (suc (n + 0)) x) a)))) -- works
  -- gcd (suc a) (suc b) = right (fst (GCD (suc a) (suc b) (left (a , {!!}))))

  test-GCD : ∃ λ x → gcd 12 16 ≡ right (4 , x)
  test-GCD = {!!}
```
