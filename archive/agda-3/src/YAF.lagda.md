
```agda
module YAF where
```

Interpretation principles:

There are three types:
* Input : Set
* Output :



```agda
open import Prelude

∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃_ = Σ _

```







{-
There's a problem with how CSV files are usually specified. A human looking at a CSV can become confused. Consider:

1 , two , "buckle my
2 , three , " , shoe

The above is actually one row of four entries, not two rows or something invalid.

Consider:

1 , two , "buckle my
2 , three , "shoes"

The above is probably invalid, as it seems to
-}
{-
Specfications for CSV file
entry := nill ∨ string ∨
CSV = List (List

Specifications for nested comment

nested-comment-start
nested-comment := nested-comment-start * comment-body *
comment-body :=

For any given annotation, we want just one way of creating the annotation. That is, for (a1 : Annotation i o1) → (a2 : Annotation i o2) → o1 ≡ o2 × a1 ≡ a2


-}

```agda
module InterpretedCSVString where

  open import Agda.Builtin.String
  open import Agda.Builtin.Char
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality
  open import Prelude

  data CharAnnotation : List Char → Char → Set where
    regular : ∀ c → (c ≡ '\\' → ⊥) → CharAnnotation (c ∷ []) c
    escaped : ∀ c → CharAnnotation ('\\' ∷ c ∷ []) c

  data StringAnnotation : List Char → List Char → Set where
    [] : StringAnnotation [] []
    _∷_ : ∀ {cs cs' xs xs'} → CharAnnotation cs cs' → StringAnnotation xs xs' → StringAnnotation (cs ++ xs) (cs' ∷ xs')

  data BadStringAnnotation : List Char → List Char → Set where
    [] : BadStringAnnotation [] []
    escaped : ∀ c xs → BadStringAnnotation ('\\' ∷ c ∷ xs) (c ∷ xs)
    regular : ∀ c xs → (c ≡ '\\' → ⊥) → BadStringAnnotation (c ∷ xs) (c ∷ xs)

  data CSVString : List Char → List Char → Set where
    csvstring : ∀ i s s' → StringAnnotation s s' → i ≡ ('"' ∷ s ++ "\"") → CSVString i s'

  data BadCSVString : List Char → List Char → Set where
    csvstring : ∀ i s s' → BadStringAnnotation s s' → i ≡ ('"' ∷ s ++ "\"") → BadCSVString i s'

  data Whitespace : List Char → ⊤ → Set where
    [] : Whitespace [] tt
    whitespace : ∀ ws → Whitespace ws tt → Whitespace (' ' ∷ ws) tt

  data CSVColumn : List Char → Maybe (List Char) → Set where
    nullary : ∀ ws → Whitespace ws tt → CSVColumn ws nothing
    unitary : ∀ ws1 cs cs' ws2 → Whitespace ws1 tt → CSVString cs cs' → Whitespace ws2 tt → ∀ i → i ≡ ws1 ++ cs ++ ws2 → CSVColumn i (just cs')
{-
  data CSVRow : List Char → List (Maybe (List Char)) → Set where
    [] : ∀ s → CSVColumn s nothing → CSVRow
    nullary : ∀ ws → Whitespace ws tt → CSVRow ws []
    unitary : ∀ ws1 cs cs' ws2 → Whitespace ws1 tt → CSVString cs cs' → Whitespace ws2 tt → ∀ i → i ≡ ws1 ++ cs ++ ws2 → CSVRow i (cs' ∷ [])
    -- comma : ∀ i1 i2 →
-}
```

{-

What might be a problem?

Want to interpret as an output: space followed by quote

"","" -- is this two empty strings? or is it a string with a comma inside?

If it's two empty strings, then how do we write a string with a comma inside?

If it's a string with a comma inside, how do we write two empty strings?

With CSVString, we would say that it's two empty strings and that to write a string with a comma inside, we write "\",\"". But with BadCSVString ... ?
-}

```agda
  record Interpreter {Input : Set} {Output : Set} (Annotation : Input → Output → Set) : Set where
    field
      listen : (input : Input) → Dec (∃ Annotation input)
      speak : (output : Output) → ∃ flip Annotation output
```

Let's see if we can prove that BadCSVString is really bad. I.e. that we can't make a proper interpreter for it.

```agda
  bad-is-bad : ¬ (Interpreter BadCSVString)
  bad-is-bad record { listen = listen ; speak = speak }
   with speak (' ' ∷ '"' ∷ []) | listen (fst (speak (' ' ∷ '"' ∷ [])))
  bad-is-bad record { listen = listen ; speak = speak } | .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl | yes (h , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) [] .h x ())
  bad-is-bad record { listen = listen ; speak = speak } | .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl | yes (h , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) [ x₂ ] .h x ())
  bad-is-bad record { listen = listen ; speak = speak } | .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl | yes (h , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) (x₂ ∷ [ x₃ ]) .h x ())
  bad-is-bad record { listen = listen ; speak = speak } | .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl | yes ([] , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) (.'\\' ∷ .' ' ∷ [ .'\"' ]) .[] () refl)
  -- "\ ""
  … | .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl
    | yes (.' ' ∷ .([ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) (.'\\' ∷ .' ' ∷ [ .'\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl) = {!!}
  bad-is-bad record { listen = listen ; speak = speak } | .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl | yes (.'\\' ∷ .(' ' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) (.'\\' ∷ .' ' ∷ [ .'\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) (regular .'\\' .(' ' ∷ [ '\"' ]) x) refl) = {!!}
  bad-is-bad record { listen = listen ; speak = speak } | .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .('\\' ∷ ' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (escaped .' ' .([ '\"' ])) refl | yes (h , csvstring .('\"' ∷ '\\' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) (x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ s) .h x x₁) = {!!}
  bad-is-bad record { listen = listen ; speak = speak } | .('\"' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) , csvstring .('\"' ∷ ' ' ∷ '\"' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) .(' ' ∷ [ '\"' ]) (regular .' ' .([ '\"' ]) x) refl | yes (h , ph) = {!!}
  bad-is-bad record { listen = listen ; speak = speak } | s , ps | no ¬h = ¬h (_ , ps)
```
