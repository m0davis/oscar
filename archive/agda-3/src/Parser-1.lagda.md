
```agda
open import Agda.Builtin.List
open import Data.Product
```

We'd like to construct a verified parser. What does that mean?

Let's try a simple example.

A simple example. We read a character, check that it is a digit from '0' to '9', and interpret it as a natural number if it's a digit, but if it isn't a digit, fail. Oh, and I forgot to mention, '0' should be interpereted as 0, '1' as 1, etc.

Let's try to spell this out.

We will assume that characters are represented by `Char` and natural numbers are represented by `Nat`.
```agda
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Nat using (Nat)
```

```agda
```

Let's define `Digitalchar` to represent the set of all characters that represent digits, and `Digitalnat` to represent the set of all natural numbers that represent digits.

```agda
data Digitalchar : Char → Set where
  digit0 : Digitalchar '0'
  digit1 : Digitalchar '1'
  digit2 : Digitalchar '2'
  digit3 : Digitalchar '3'
  digit4 : Digitalchar '4'
  digit5 : Digitalchar '5'
  digit6 : Digitalchar '6'
  digit7 : Digitalchar '7'
  digit8 : Digitalchar '8'
  digit9 : Digitalchar '9'

data Digitalnat : Nat → Set where
  digit0 : Digitalnat 0
  digit1 : Digitalnat 1
  digit2 : Digitalnat 2
  digit3 : Digitalnat 3
  digit4 : Digitalnat 4
  digit5 : Digitalnat 5
  digit6 : Digitalnat 6
  digit7 : Digitalnat 7
  digit8 : Digitalnat 8
  digit9 : Digitalnat 9
```

```agda
digit-correspondence : List (∃ Digitalchar × ∃ Digitalnat)
digit-correspondence =   ((, digit0) , (, digit0))
                       ∷ ((, digit1) , (, digit1))
                       ∷ ((, digit2) , (, digit2))
                       ∷ ((, digit3) , (, digit3))
                       ∷ ((, digit4) , (, digit4))
                       ∷ ((, digit5) , (, digit5))
                       ∷ ((, digit6) , (, digit6))
                       ∷ ((, digit7) , (, digit7))
                       ∷ ((, digit8) , (, digit8))
                       ∷ ((, digit9) , (, digit9))
                       ∷ []
```

A human will have to verify this code for semantic correctness. The following conditions must be met:

* soundness: Each pair (c , d) in the list must be such that the Char c "corresponds to" the digit d
* -- anything else? do we need the list to be complete? in a certain order?

So, we've got this complete and correct correspondence between the digital representors. We can even encode them as follows:

```agda
representor-encoding : List (Char × Nat)
representor-encoding = {!!}

abstract
  Dchar = ∃ Digitalchar
  Dnat = ∃ Digitalnat
  dcorrespondence : List (Dchar × Dnat)
  dcorrespondence = digit-correspondence
  _ = {!dcorrespondence!}

_ = {!dcorrespondence!}
```



```agda
zero-char : Char
zero-char = '0'
```
