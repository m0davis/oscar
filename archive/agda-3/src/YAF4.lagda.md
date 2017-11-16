
Wherein I think I am trying to build a parsimonious parser.

Some preliminaries that could be put elsewhere.

```agda
open import Prelude

∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃_ = Σ _

data IsYes {a} {P : Set a} : Dec P → Set a where
  yes : (p : P) → IsYes (yes p)

getProof : ∀ {a} {P : Set a} → {d : Dec P} → IsYes d → P
getProof (yes p) = p
```

The state-of-the-art so far.

```agda
record Interpreter {source : Set} {target : Set} (translation : source → target → Set) : Set where

  field
    interpret : (s : source) → Dec $ ∃ translation s -- possibly generate a translation into the target language (or show that no translation is possible)
    restate : (t : target) → ∃ λ s → ∃ λ (r : translation s t) → interpret s ≡ yes (t , r) -- for any statement from the target language, there's a statement in the source that is interpreted as the original statement in the target language. The restated source is a fix-point of restate ∘ interpret.
    translation-is-functional : ∀ s t1 t2 → translation s t1 → translation s t2 → t1 ≡ t2 -- no ambiguities: multiple interpretations are not possible.
```

(As an alternative to `translation-is-functional`, we could allow for ambiguity and place this into the definition of `interpret`. Perhaps we should generate a stream of interpretations. We could possibly use this to try interpreting a resolvable ambiguity: e.g. we don't know if '*' delimits code or comments, we try to parse a number in "blah * 12 * 50". In that case, we can conclude that " 12 " represents the number and "blah " and " 50" represent comments. how about misspellings?!m What can we infer about how to interpret something given a restatement and the fact that it is a fixed-point? how about vice-versa? how much something can we get out of nothing? consider "So you want to link your State data" and the EM algorithm. Understanding probable probabilities may be important here.)

Thoughts about what more to do.
  Compose Interpreters.
  See about tracking source code locations.

In parsing a literate agda file, we would like to identify the following as parts of the file, with all of them together (perhaps having several of some) making up the entire file.

  end-of-file
  literate-block
  code-block
  beginning-of-code-block
  end-of-code-block

Here are some ideas for how to delimit code-blocks.

1. Much like (maybe exactly like) the existing parser: Place "```agda" on its own line to indicate the start of a code-block. Place "```" on its own line to indicate its end. It turns out that this makes some otherwise-valid Agda code blocks invalid, but such cases are exected to be rare and there are minor changes one could make to restore the code to its original meaning. Thus, this places a slight strain on `restate`. If, say we had defined an `Interpreter`, for translating `String`s into Agda Language structures, and the interpreter `restate`d literal strings using actual new-lines (instead of escaped sequences, "\n"), then we would not be able to compose such an interpreter with our one for translating `String`s into LiterateAgda Language structures. Also note that it would disallow the use of a linter with an option to place new function identifiers on their own line.

2. To avoid such problems entirely, we might try the following: At the top of every lagda file, we include a special region where the user specifies the given strings that are to delimit the start and end of the code blocks.

It occurs to me that the notion of composition as used above is a bit confused: we can't compose string-to-lagda with string-to-agda. Better is to consider the following translations:

parseLagda : String → Lagda → Set -- input is a .lagda.md file, output is data
forgetLiterate : Lagda → String → Set -- output is an .agda file
parseAgda : String → Agda → Set -- input is an .agda file, output is data

So, missing from the above discussion was the notion that there would be this middling "forgetful" translation, which drops the literate stuff in translating to a .agda file.

Now we can say that the problem with the first approach above is that it does not allow for this modular approach, because there is no way to define `restate` for forgetLiterate, as there are some `String`s that contain, say, "```" on its own line. To take the first approach, we could use the following translations:

parseLagda : String → Lagda → Set -- input is a .lagda.md file, output is data
forgetLiterate : Lagda → Σ String NoLagdaDelimiters → Set -- output is an .agda file that does not contain .lagda.md delimiters, such as "```" all on its own line
parseAgda : String → Agda → Set -- input is an .agda file, output is data
parseAgda' : Σ String NoLagdaDelimiters → Agda → Set -- input is an .agda file with certain conditions, output is data

If we use parseAgda', we can easily compose. If we use parseAgda, we have a problem when it comes to `restate`. But parseAgda is "nice" in that it is permissive in its input: there are fewer requirements when it comes to defining `restate` for parseAgda than for parseAgda'. Having more requirements increases the possibility that, with everything else set in place, we come to define `restate` for parseAgda' and find it impossible. For example, imagine that the structure of `Agda` includes a `String` representing string literals (rather than an `EscapedString` representation).

Say we go ahead and write parseAgda'. And say it turns out that `parseAgda'`s `interpret` does not use the `NoLagdaDelimiters` premise. Then we'll be stuck rewriting the same function (copy-and-paste or use a macro, but leave out the premise). Alternatively, we would have to first fix-up the code to guarantee there are no such delimiters but then we gotta worry that our fix-up didn't screw anything up. So the approach of writing parseAgda' as the primary interpreter seems backwards. We'd rather write an interpreter that can interpret *more*. That would be being "liberal in what we accept". The fact that we would need to be careful when defining `restate` for `parseAgda` corresponds to the principle of being "conservative in what we produce". The fact that being liberal in this case is easy corresponds to the fact that [a .lagda.md file transmits no information about its code blocks] ... conservative is easy because (why?) the designs for an .agda are already liberal in what they accept.

A trouble with the second approach is that the format of the input file is not really an .md file. We would like to add-on another layer to compile the .lagda.pseudo-md into .lagda.md. The idea will be to make the following compositions. (The above Lagda is now Plagda.)

parsePlagda : String → Plagda → Set
forgetPliterate : Plagda → String → Set
parseAgda : String → Agda → Set
parseMd : String → Md → Set -- uses the standard .lagda.md translation, like parseLagda above in the first approach
forgetMd : Md → Σ String NoMdDelimiters → Set -- like forgetLiterate above
parseRestrictedAgda : Σ String NoMdDelimiters → Agda → Set

Wait, this won't work b/c someone could include a .lagda.md delimiter in a .agda comment.

I feel like I'm fumbling here because I haven't been clear about what the requirements are. And it seems some of the floating requirements are in conflict with each other.

* all existing .lagda.md files must be interpreted as Agda does now
* users must be able to take any working .agda file and drop it into a .lagda.md file with a simple copy-paste (and perhaps some additional details at the top, specifying the delimiters)

The above are incompatible. Going forward, I would like to go with the first bullet-point, which means sticking with approach (1.) above. Insofar as we deal with these translations:

parseLagda : String → Lagda → Set -- input is a .lagda.md file, output is data
forgetLiterate : Lagda → Σ String NoLagdaDelimiters → Set -- output is an .agda file that does not contain .lagda.md delimiters, such as "```" all on its own line
parseAgda : String → Agda → Set -- input is an .agda file, output is data
parseAgda' : Σ String NoLagdaDelimiters → Agda → Set -- input is an .agda file with certain conditions, output is data

...we would initially write interpret for parseAgda and restate for parseAgda'. Then, to complete the Interpreters, we would use each of the other's for the one. As a data structure, we would use one with the type of `parseAgda`.

Let's get a feel for how we can prove some simple things, compare to the classical counterpart, and see how we might automate.

```agda
module SimpleArithmeticProofs where

  left-multiplicative-zero-property : (n : Nat) → 0 *N n ≡ 0
  left-multiplicative-zero-property = λ (n : Nat) → refl

  right-multiplicative-zero-property : (n : Nat) → n *N 0 ≡ 0
  right-multiplicative-zero-property = λ { zero → refl ; (suc n) → right-multiplicative-zero-property n }
```

Here is a classical proof of the left version:

⊢ ∀ n → 0 *N n ≡ 0

Here is a classical proof of the right version:

⊢ ∀ n → 0 *N n ≡ 0
⊢ 0 *N n ≡ 0
⊢ ∀ m n → suc n *N m ≡ m +N n *N m
⊢ ∀ n → 0 +N m ≡ m
⊢ ∀ m n → suc n +N m ≡ suc (n +N m)
⊢ ∀ n → ¬ (n ≡ 0) → ∃ m → n ≡ suc m
⊢ ∀ P → P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n

⊢ n *N 0 ≡ 0 ⊢ n *N 0 ≡ 0
⊢ n *N 0 ≡ 0 ⊢ 0 +N (n *N 0) ≡ 0
⊢ n *N 0 ≡ 0 ⊢ suc n *N 0 ≡ 0
⊢ n *N 0 ≡ 0 → suc n *N 0 ≡ 0
⊢ ∀ n → n *N 0 ≡ 0 → suc n *N 0 ≡ 0
⊢ ∀ n → n *N 0 ≡ 0

And now for a try at an intuitionistic proof. For a little more simplicity, we'll use addition instead of multiplication.

recNat : Π Universe (Π (var 0) (Π (Π Nat (Π (var 2) (var 3)

add : Π Nat (Π Nat Nat)
add ≡ recNat (Π Nat Nat) (lamda (var 0))
rmzp : Π Nat (Nat (Id Nat (multiply (var 0) zeroNat))

agrh! I can't read DeBruijn.

primitive
  indNat : (C : Nat → Set) → C natZero → ((n : Nat) → C n → C (natSucc n)) → (n : Nat) → C n
  indId : (C : (x y : A) → Id A x y → Set)

We have already

addNat : Nat → Nat → Nat
addNat :≡ indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m))

Our goal is to find a defining equation for

razp : (n : Nat) → Id Nat (addNat n zeroNat) zeroNat

Somehow or other, we should be able to say that we're looking for

razp : (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat

To be more specific, we're actually looking for some way of deriving something of the form

() ⊢ ?? : (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat

Now, let's look for rules that allow us to form something of the above type. We find the following:

Subst₁ fits, but this is clearly a kind of "do nothing", so we'll skip it for now.
One of the unnamed equivalence rules also fits, but it's also clearly skippable.
Π-Intro fits, with Γ = (), x = n, A = Nat, B = Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat. We would then have an interest in finding n : Nat ⊢ ?b : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat in order to conclude () ⊢ λ (n : Nat) → ?b.
Π-Elim fits, but it feels like this should not be used here. I think the use of Π-Elim should be similar to the use of Universal Instantiation. That is, it is used only in forwards inference. But note that it carries an additional burden that we cannot simply make one inference and be done, but rather it is parameterised on a : A. The same sorts of comments might be made about the above-mentioned Subst₁ and equivalence rules. Another thought is that it *could* be used in backwards inference *if* we were looking for something of the form of an application (but in this case, we don't know what form the expression will take).
Σ-Elim fits, but again, we will skip because it clearly does not meet some requirements that would make it make sense to use it.
+-Elim fits, but skip it.
0-Elim fits. In this case, should we really skip it? In fact, should we have skipped any of the above? Perhaps we should allow all of the above so long as they make some increase in the length of the lamda expression (rather than the "do nothing" stuff). We thus might continue the backwards search in a kind of "even-handed" way to help guarantee completeness. In this case, we would generate interests in () ⊢ ?? : 0 and x : 0 ⊢ some-big-thing-which-we-don't-know-until-we-know-the-first-thing-we're-interested-in. Okay, so *clearly* (!) this is a case where we want some additional requirements before we make a backwards inference. In particular, we need it that Γ : ?? : 0 for some ?. In this case, we don't have it.
(Going back through the above, we skip Π-Elim because we don't yet have ... what?
Not yet sure why, but it seems that none of these elimination rules should be used in (purely) backwards inference. Perhaps it is best explained via a semantic model. For example, consider a classical first-order deduction system. Given an interest in ∀x(φ), it seems silly to adopt interest in ∀y∀x(φ). That would be like saying: I wonder if all dogs are friendly; in other words, is it the case that for each dog d, d is friendly? well, to answer this question, I shall adopt interest in the proposition that for each dog d', it is the case that for each dog d, d is friendly. It's true that establishing the one will lead to the other, but it also seems obviously silly to do this. Proving silliness is another matter. I guess a clue is that it does not "reduce" the problem along any sort-of "reasonable" measure. Enough hand waving.
Nat-Comp₂ is interesting. There is a natSucc within our goal type, but we are not looking for a judgement of equality, but rather one of type.
Okay, let's skip the obvious stuff.

We start with interest in

() ⊢ ?1 : (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat

And by Π-Intro, we now have interest in

(n : Nat) ⊢ ?2 : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat

and we have it that

?1 ≡ λ (n : Nat) → ?2

But now I seem to be stuck because I cannot use Id-Elim. Perhaps there was something about one of those Nat rules that might have done the trick. We are, after all, trying to case split.

Really should explain why this works: we use Nat-Elim.

We have it that

(n : Nat) ⊢ Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat : Set

Notice that we can somehow rewrite this as

(x : Nat) ⊢ Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat : Set

So we can use Nat-Elim with Γ = (n : Nat), C = Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat, and n = n.

We thus adopt interest in

(n : Nat) ⊢ ?3 : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat zeroNat) zeroNat
(n : Nat , x : Nat , y : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat) ⊢ ?4 : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) (natSucc x) zeroNat) zeroNat
(n : Nat) ⊢ n : Nat

and we have it that

?2 = indNat (λ x → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat)
            ?3
            λ x y → ?4
            n

Taking the interest involving ?3 above, we are again stuck unless we can reduce the term involving indNat. Now here is where we must somehow put ourselves in a position to use Nat-Comp₁. I had said before that we were stuck and could not use Id-Elim, but maybe I could have actually proceeded. Going back to that now, we can use Id-Elim with Γ = (n : Nat), C = Id Nat a b, a = indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat, b = zeroNat, A = Nat, ... but no, we are indeed stuck here, because we would need to adopt interest in Γ ⊢ ?? : Id Nat a b, which is exactly where we came from.

We would want to somehow adopt interest in something like

indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat zeroNat ≡ zeroNat

and then use Nat-Comp₁ to conclude it.

Our strategy could be to say that whenever we have an interest in something, we attempt first to normalise it. So this interest would trigger whatever forwards reasoning tends to normalise stuff, and this would include Nat-Comp₁. The hook would be that equivalence rule previously mentioned that I decided not to use. Now we can say that it's okay to use that rule so long as we are searching for a reduction (A would be a reduction of B), and then we can note (via the structure of the judgemental equality itself) that Nat-Comp₁'s rhs is a reduction of its lhs. Presumably (though it's less obvious to me), the same can be said for Nat-Comp₂.

Let's try the one we know must "work" and then try the same strategy on the one we know doesn't. Starting from

(n : Nat) ⊢ ?3 : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat zeroNat) zeroNat

we use the equivalence rule with B = Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat zeroNat) zeroNat, and a = ?3 to adopt interest in

(n : Nat) ⊢ ?5 : ?6
(n : Nat) ⊢ ?6 ≡ Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat zeroNat) zeroNat : Set

...well, let's just say for now that we normalise the types in which we have interest.

So, having adopted interest in

(n : Nat) ⊢ ?3 : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat zeroNat) zeroNat
(n : Nat , x : Nat , y : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat) ⊢ ?4 : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) (natSucc x) zeroNat) zeroNat
(n : Nat) ⊢ n : Nat

we use Nat-Comp₁ to get that

indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat
  ≡ λ n → n

so, rewriting, we get

(n : Nat) ⊢ ?3 : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) zeroNat zeroNat) zeroNat
(n : Nat) ⊢ ?3 : Id Nat ((λ n → n) zeroNat) zeroNat
(n : Nat) ⊢ ?3 : Id Nat zeroNat zeroNat

and we use Nat-Comp₂ to get

indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) (natSucc x)
  ≡ (λ n g m → natSucc (g m)) x (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x)
  ≡ (λ m → natSucc ((indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x) m))

so, rewriting, we get

(n : Nat , x : Nat , y : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat) ⊢ ?4 : Id Nat ((λ m → natSucc ((indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x) m)) zeroNat) zeroNat
(n : Nat , x : Nat , y : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat) ⊢ ?4 : Id Nat (natSucc (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat)) zeroNat

So, the new set of adopted interests is

(n : Nat) ⊢ ?3 : Id Nat zeroNat zeroNat
(n : Nat , x : Nat , y : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat) ⊢ ?4 : Id Nat (natSucc (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat)) zeroNat
(n : Nat) ⊢ n : Nat

At this point, let's review what we've got, and add some labels for the various interests and equations. I will use "I" to label interests and "E" to label equations.

I01. () ⊢
     ?1 :
     (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat
I02. (n : Nat) ⊢
     ?2 :
     Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) n zeroNat) zeroNat
E01. ?1 ≡ λ (n : Nat) → ?2
I03. (n : Nat) ⊢
     ?3 :
     Id Nat zeroNat zeroNat
I04. (n : Nat , x : Nat , y : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat) ⊢
     ?4 :
     Id Nat (natSucc (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat)) zeroNat
I05. (n : Nat) ⊢ n : Nat
E02. ?2 ≡ indNat (λ x → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → natSucc (g m)) x zeroNat) zeroNat)
                 ?3
                 (λ x y → ?4)
                 n

I05 is easily solved, as is (now) I03. What about I04? Something must have gone wrong. It looks false! We are equating a natSucc with a zeroNat.

Let's try deriving I04 again. ... hah ... the problem was I was trying to prove that n + 0 = 0. Let's instead try n + 0 = n.

I01. Goal
  () ⊢
  ?I01 :
  (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) n
I02. Π-Intro, I01
  .1 () ⊢
     ?I01 ≡
     λ (n : Nat) → ?I02.1 :
     (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) n
  .2 (n : Nat) ⊢
     ?I02.1 :
     Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) n

The rules are not much guidance here, so I need to be creative. I would like to derive I02.2, but to do that we need at least to show that

(n : Nat) ⊢ indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat ≡ n : Nat

Then we could use Id-Intro-Eq to derive

(n : Nat) ⊢ refl Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) ≡ refl Nat n : Id Nat n n

and then use Id-Form-Eq to derive

(n : Nat) ⊢ Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) n ≡ Id Nat n n

and then use Equiv-Elim₂ to derive

(n : Nat) ⊢ refl Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) ≡ refl Nat n : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) n

and finally use the "another property of our type system" to derive

(n : Nat) ⊢ refl Nat n : Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n g m → succNat (g m)) n zeroNat) n


So, let's try this again.

In addition to everything from Appendix 2, I want to specify that we have:

=-INTRO-EQ :     Γ ⊢ A : Uᵢ ; Γ ⊢ a ≡ b : A
             --------------------------------
               Γ ⊢ reflₐ ≡ refl_b : a =_A b

≡-ELIM₁ :   Γ ⊢ a ≡ b : A
           ---------------
             Γ ⊢ a : A

≡-ELIM₂ :   Γ ⊢ a ≡ b : A
           ---------------
             Γ ⊢ b : A

Packaging this into something useful,

          Γ ⊢ A : Uᵢ ; Γ ⊢ a ≡ b : A
    --------------------------------------
         Γ ⊢ reflₐ ≡ refl_b : a =_A b
-------------------------------------------------------
            Γ ⊢ reflₐ : a =_A b

I will also reformulate the way I do these interest-driven proofs. I will write judgemental equalities as being built-up on the same line.

And so now maybe we can prove this goal:

>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> well, not quite so easy yet
>> I01. Goal
>>   () ⊢
>>   ?I01 :
>>   (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n f m → succNat (f m)) n zeroNat) n
>> I02. Π-Uniq, I01
>>   () ⊢
>>   ?I01 ≡ (λ (x : Nat) → ?I01 x) :
>>   (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n f m → succNat (f m)) n zeroNat) n
>> I03. Π-Uniq, I02
>>   () ⊢
>>   ?I02 ≡ ?I01 :
>>   (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n f m → succNat (f m)) n zeroNat) n
>> I02. Π-Intro, I01
>>   .1 () ⊢
>>      ?I01 ≡
>>      λ (n : Nat) → ?I02.1 :
>>      (n : Nat) → Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n f m → succNat (f m)) n zeroNat) n
>>   .2 (n : Nat) ⊢
>>      ?I02.1 :
>>      Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n f m → succNat (f m)) n zeroNat) n
>> I03. ≡-ELIM₂, I02
>>   .1 (n : Nat) ⊢
>>      ?I02.1 ≡ ?I03.1:
>>      Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n f m → succNat (f m)) n zeroNat) n
>>   .2 (n : Nat) ⊢
>>      ?I02.1 ≡ ?I03.1:
>>      Id Nat (indNat (λ _ → Nat → Nat) (λ n → n) (λ n f m → succNat (f m)) n zeroNat) n
>>
>>
>>      ?I02.1 ≡ refl :
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

(Continued far below).

```agda
```

It's time to prove GCD.

```agda
module ProvingGCD where

  -- "a divides b" or "a is a divisor of b" or "b is divided by a" or "b is divisible by a"
  DIV : (a b : Nat) → Set
  DIV a b = ∃ λ n → b ≡ a *N n

  CD : (cd a b : Nat) → Set
  CD cd a b = DIV cd a × DIV cd b

  LESSTHAN : (a b : Nat) → Set
  LESSTHAN a b = ∃ λ k → b ≡ suc k +N b
```

All numbers are divisors of 0. That is to say, DIV∙0 is Nat.

```agda
  DIV∙0≡Nat : (n : Nat) → DIV n 0
  DIV∙0≡Nat n = 0 , {!!}
```

But DIV∙1 is just 1. DIV∙2 is 1 and 2, etc. So the only weird case is where both are 0.

```agda
  GCD : (a b : Nat) → ∃ λ gcd → CD gcd a b × ∀ cd → CD cd a b → Either (cd ≡ gcd) (LESSTHAN cd gcd)
  GCD zero zero = {!!} , (({!!} , {!!}) , {!!} , {!!}) , λ { cd ((fst₁ , snd₂) , fst₂ , snd₁) → {!!}} -- but we know that (Σ Nat (λ k → ?0 ≡ suc (k + ?0))) is impossible! -- and we can also surmise that cd ≡ ?0 is unfullfillable
  GCD zero (suc b) = {!!}
  GCD (suc a) zero = {!!}
  GCD (suc a) (suc b) = {!-t 12 -c!}
```
