```agda
{-# OPTIONS --allow-unsolved-metas #-}
```
I had thought that, in all cases where an argument is applied to a function, any unmentioned preceding instance arguments would be filled by agda as `{{it}}`. For example, given `foo : {{_ _ : _}} -> _ -> _`, `foo x` is equivalent to `foo {{it}} x`, which in turn is equivalent to `foo {{it}} {{it}} x`. But it turns out that isn't the case, as shown below.
```agda
{-# OPTIONS --instance-search-depth=10 #-}
{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc:30 #-} -- include to see "you shouldn't see this" in the debug output

open import Agda.Primitive

it : ∀ {a} {A : Set a} {{x : A}} -> A
it {{x}} = x

infixr 5 _,_
postulate
  Pair : ∀ {a} (A : Set a) {b} (B : Set b) -> Set (a ⊔ b)
  _,_  : ∀ {a} {A : Set a} {b} {B : Set b} -> A -> B -> Pair A B

data Constraint {a} {A : Set a} (x : A) : Set where
  mkConstraint : Constraint x

record Inner {l a} {A : Set a} (x : A) (_ : Constraint x) (C : Set l) : Set l where
  field
    value : C

Class : ∀ {l a} {A : Set a} (x : A) (C : Set l) -> Set l
Class x C = Inner x mkConstraint C

FunctionClass = λ
  {a} (A : Set a)
  -> Class A (A -> A)

DiagonalClass = λ
  {i} {I : Set i}
  {r} (R : I -> I -> Set r)
  x
  -> Class (R , x) (R x x)

DiagonalFunctionClass = λ
  {i} {I : Set i}
  {r} (R : I -> I -> Set r)
  x
  -> Class (R , x) (R x x -> R x x)

postulate
  toDiagonalFunctionClass : ∀
    {i} {I : Set i}
    {r} {R : I -> I -> Set r}
    {{iD : ∀ {x} -> DiagonalClass R x}}
    -> ∀ {x} -> DiagonalFunctionClass R x

DiagonalPropertyType = λ
  {i r p} {I : Set i}
  (R : I -> I -> Set r)
  (P : ∀ x -> R x x -> Set p)
  -> ∀ x (d : R x x) -> P _ d

DiagonalPropertyClass = λ
  {i r p} {I : Set i}
  (R : I -> I -> Set r)
  (P : ∀ x -> R x x -> Set p)
  (C : FunctionClass I)
  -> Class (R , P , C) (DiagonalPropertyType R P)

diagonalProperty : ∀
  {i r p} {I : Set i}
  {R : I -> I -> Set r}
  {P : ∀ x -> R x x -> Set p}
  {{C : FunctionClass I}}
  {{iDP : DiagonalPropertyClass R P C}}
  -> DiagonalPropertyType R P
diagonalProperty {{iDP = iDP}} = Inner.value iDP

works-1 works-2 fails : ∀
  {r p} {I : Set}
  {R : I -> I -> Set r}
  {P : ∀ x -> R x x -> Set p}
  (C : FunctionClass I)
  {{iDP : DiagonalPropertyClass R P C}}
  -> DiagonalPropertyType R P

works-1 C x d =
  let instance iC = C
  in diagonalProperty _ d

works-2 C x d =
  let instance iC = C
               iDF = toDiagonalFunctionClass
  in diagonalProperty {{it}} _ d

fails C x d =
  let instance iC = C
               iDF = toDiagonalFunctionClass
  in {!diagonalProperty _ d!} -- Instance search depth exhausted
```

The error is

    Instance search depth exhausted (max depth: 10) for candidate
    .iDP : DiagonalPropertyClass {lzero} {.r} {.p} {.I} .R .P C
    when checking that _ d are valid arguments to a function of type
    {i r p : Level} {I : Set i} {R : I → I → Set r}
    {P : (x₁ : I) → R x₁ x₁ → Set p} {{C = C₁ : FunctionClass {i} I}}
    {{iDP : DiagonalPropertyClass {i} {r} {p} {I} R P C₁}} →
    DiagonalPropertyType {i} {r} {p} {I} R P

A similar error arises from the following test case:
```agda
postulate
  r p : Level
  I : Set
  R : I -> I -> Set r
  P : ∀ x -> R x x -> Set p
  C : FunctionClass I
  instance iDP : DiagonalPropertyClass R P C

instance iC = C
instance iDF = toDiagonalFunctionClass

?i : Level
?I : Set ?i
?R : ?I -> ?I -> Set r
?P : ∀ x -> ?R x x -> Set p
?C : FunctionClass ?I
?iDP : DiagonalPropertyClass ?R ?P ?C

?i = _
?I = _
?R = _
?P = _

-- reverse the order of the following two lines to get the "instance search depth exhausted" error
?C = it
?iDP = it
```

The error is:

    Instance search depth exhausted (max depth: 10) for candidate
    iDP : DiagonalPropertyClass {lzero} {r} {p} {I} R P C
    when checking that the expression it has type
    DiagonalPropertyClass {?i} {r} {p} {?I} ?R ?P ?C
