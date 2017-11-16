```agda : String

```agda
module TypeTheory where

-- open import Agda.Builtin.String

```agda : {!!}
```agda = "\n``` \n"

``` : {!!}
``` = 3

```

```agda
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
```

A `Variable n` is a variable in a context of n variables bound by abstractions (nested n times), such that `zero` is the variable bound by the nearest containing abstraction in the current context, and `suc n` is the one bound by nearest containing abstraction to the context binding a variable `n`.

```agda
open import Data.Fin

Variable = Fin
```

A `Term n` is a term in a context similar to that for `Variable n`.

```agda
data Term (n : Nat) : Set where
  variable : Variable n → Term n
  abstraction : Term (suc n) → Term n
  application : Term n → Term n → Term n
```

A variable `v` bound by some abstraction and referrable to in the current context may be also be referred to in a sub-context. In this case, we increment its value by 1.

```agda
weakenVariable : ∀ {n} → Variable n → Variable (suc n)
weakenVariable v = suc v
```

...and similarly for `Term`s.

```agda
weakenTerm : ∀ {n} → Term n → Term (suc n)
weakenTerm (variable n) = variable (weakenVariable n)
weakenTerm (abstraction M) = abstraction (weakenTerm M)
weakenTerm (application M E) = application (weakenTerm M) (weakenTerm E)
```

Given an `abstraction f : Term n` and an `x : Term n`, we may apply `f` to `x` as in `application (abstraction f) x`, thereby discharging the `abstraction`. This is known as β-reduction, or, equivalently, to substitution of a single variable (the one brought into context by the `abstraction`) for the applied expression, `x`. `β-reduce f x` is the result of a β-reduction of `application (abstraction f) x`. We may also think of `β-reduce f x` as the substitution of the 0ᵗʰ variable of f for x.

```agda
module WRONG where
  β-reduce : ∀ {n} → Term (suc n) → Term n → Term n
  β-reduce (variable zero) E = E
  β-reduce (variable (suc n)) E = variable n
  β-reduce (abstraction M) E = abstraction (β-reduce M (weakenTerm E)) -- wrong
  {- the above (wrongly) substitutes the 0ᵗʰ variable of M instead of the 1ˢᵗ  -}
  β-reduce (application M N) E = application (β-reduce M E) E
```

Another idea is to start with a notion of simultaneous substitution. Given a context of n variables, we simultaneously substitute all n variables for n given terms. A substitution in t for n terms where the iᵗʰ term is a variable standing for the iᵗʰ context variable results in the same term, t.

But is it necessary to simultaneously substitute to achieve β-reduction?

??? Why not reduce

flip = λ f x y → f y x
_∘_ = λ g f x → g (f x)

???
consider flip f :
(λ f x y → f y x) f
(λ x y → f y x)


consider flip ∘ flip :
(λ g f x → g (f x))(λ f x y → f y x)(λ f x y → f y x)
(λ g f x → g (f x))(λ f' x' y' → f' y' x')(λ f'' x'' y'' → f'' y'' x'')
(λ f x → (λ f' x' y' → f' y' x') (f x))(λ f'' x'' y'' → f'' y'' x'')
(λ x → (λ f' x' y' → f' y' x') ((λ f'' x'' y'' → f'' y'' x'') x))
(λ x → (λ x' y' → ((λ f'' x'' y'' → f'' y'' x'') x) y' x'))
(λ f → (λ x' y' → ((λ f'' x'' y'' → f'' y'' x'') f) y' x'))
(λ f → (λ x' y' → (λ x'' y'' → f y'' x'') y' x'))
(λ f → (λ x' y' → f x' y'))
(λ f x y → f x y)


???

   consider flip flip =
   (λ f x y → f y x)(λ f x y → f y x)
   (λ x y → (λ f x' y' → f y' x') y x)
   (λ x y → (λ x' y' → y y' x') x)
   (λ x y → (λ y' → y y' x))
   (λ x y y' → y y' x)
   (λ x f y → f y x)


   add = λ suc x y →

Notice that β-reduction is like pulling abstractions upwards. Is this called "lamda lifting"?

In the `WRONG.β-reduce` above, we tried to substitute the 0ᵗʰ variable by an arbitrary expression. That failed because in a recursive call (due to an `abstraction`), we would need to substitute the 1ᵗʰ variable. We therefore gain by making a more generic function, one that substitutes an *arbitrary* variable by an arbitrary expression.

`substitute t x e` yields the term t with variable x everywhere replaced with expression e, thus yielding a term with one fewer context variable than t.

To compare variables in the given term to the given variable, we will need a decidability of equality for variables.

```agda
open import Data.Empty
open import Relation.Nullary

Decidable = Dec

_≟V_ : ∀ {n} → (x y : Variable n) → Decidable (x ≡ y)
zero ≟V zero = yes refl
zero ≟V suc _ = no λ ()
suc _ ≟V zero = no λ ()
suc x ≟V suc y with x ≟V y
… | yes x≡y = yes {!!}
… | no x≢y = {!!}
```

```agda
substitute : ∀ {n} → Variable (suc n) → Term (suc n) → Term n → Term n
substitute x (variable n) e with x ≟V n
… | yes x≡n = e
… | no x≢n = variable (punchOut x≢n)
substitute x (abstraction t) e = abstraction (substitute (weakenVariable x) t (weakenTerm e))
substitute x (application f y) e = application (substitute x f e) (substitute x y e)
```

How can we know that substitution is correct? Here are some necessary features:

  substitute zero (abstraction (variable zero)) e ≡ abstraction e
  ... more?

Having defined substitution, let's try to β-reduce. That is, let's evaluate an applications of abstractions.

(application (abstraction f) x) -->β substitute zero f x

In general, we want to apply β-reduction to terms.

The simplest unit of β-reduction is as shown above.

```agda
β-reduce : ∀ {n} → Term n → Term n
β-reduce (variable x) = variable x
β-reduce (abstraction x) = abstraction (β-reduce x)
β-reduce (application (variable v) x) = (application (variable v) (β-reduce x))
β-reduce (application (abstraction f) x) = substitute zero f (β-reduce x)
β-reduce (application (application f x) y) with β-reduce (application f x)
… | variable v = application (variable v) (β-reduce y)
… | abstraction f' = substitute zero f' (β-reduce y)
… | application f' x' = {!!} -- application v (β-reduce y)
```

A desideratum of β-reduce is that *if* a term can be put into (weak head) normal form then it does so. So, we need a notion of equivalence of `Term`s. For this, we consider all models of the function space.

For example,
  in the expression (λ f x → f x), we can model this as a function of type (A → B) → A → B.
  In the expression (λ x → x), we can model this as A → A (for any A, including such things as (B → B)).
  We consider (λ x → x)(λ y → y) = (λ y → y), and (λ x → x)(λ y → y) may be modeled by the application of ((B → B) → (B → B)) to (B → B), yielding (B → B), which is compatible with A → A.
  But when we consider (λ x → x x), let the domain of the function be A → B. Then we apply A → B to A → B, so A → B must somehow be equivalent to A.
  Another way to interpret (λ x → x x) is that it describes a function whose domain is all functions whose domain is the the set of functions. That is, if f = (λ x → x x), let
    Set₀ = set of all urelements
    Set₁ = powerset of Set₀
    A → B = { f | f ⊆ A × B , ∀ x ∈ A → (∃ w (x , w) ∈ f) × ∀ y z → (x , y) ∈ f × (x , z) ∈ f → y = z }
    Function₀ : A →₀ B = Bᴬ { f | f ⊆ A × B , ∀ w x y z → (x , y) ∈ f × (x , z) ∈ f → y = z }
    F = the set of all functions
    G = { g | g ∈ F , domain(g) = F }
    domain(f) =
    F = a subset of all functions the domain of f be F, let

Now we are interested in whether we can convert a term into weak head normal form. That is, one in which the top-level is not an application.

```agda
data WHNF {n} : Term n → Set where
  variable : (v : Variable n) → WHNF (variable v)
  abstraction : (t : Term (suc n)) → WHNF (abstraction t)
```

```agda
{-
mkVar : ∀ {n} → Nat → Variable (suc n)
mkVar zero = {!Variable.zero!}
mkVar (suc x) = {!!}

`var : ∀ {n} → Nat → Term (suc n)
`var m = variable (mkVar m)

`λ : ∀ {n} → Term (suc n) → Term n
`λ = {!!}

my-application : Term 2
my-application = `λ `λ (`var 1 `$ `var 0)

test-β-reduce : {!!} -- β-reduce (application {0}
test-β-reduce = {!!}
-}
```

```agda
data Primitive : Set where
  moveL moveR
   print1 print0
   : Primitive

g : Set
g = {!!}
-- _ = ?
```

Here's the trick to make this all worthwhile: convert a lambda expression in normal form into a real program (i.e. a program that does something).

```agda
data Normal {n} : Term n → Set where
  variable : (v : Variable n) → Normal (variable v)
  abstraction : (l : Term (suc n)) (t : Normal l) → Normal (abstraction l)
  application-variable : (v : Variable n) (a : Term n) (t : Normal a) → Normal (application (variable v) a)
  application-application : (f : Term n) (ft : Normal f) (g : Term n) (gt : Normal f) (a : Term n) (at : Normal a) → Normal (application (application f g) a)
```

I should prove that any term that contains no redexes is equivalent to a normal.

Now let's suppose we have a Normal {1}. That is, a normal with up to one free variable. Let's associate the variable with a primitive action, say "print 1 and move right". Then we can write a program like:

λ x → x x x



This would then "mean" ... what? We haven't defined application. We could take it to mean: application f g = do f, then do g. In which case the above program simply prints three 1s.

Let's try something more interesting:

actions:
  move right
  move left
  print 1
  print 0
  ?

To implement a Turing machine, say a 2-state one, let's add some other "actions". We will add
  state 1
  state 2

A Turing machine action is : tape-symbol → current-state → print-action × move-action × next-state

λ move-right move-left print-1 print-0

encoding of booleans:

true = λ a b → a
false = λ a b → b
if_then_else = λ p t e → p t e

natural numbers:

0 = λ s z → z
1 = λ s z → s z
2 = λ s z → s (s z)
suc = λ n → λ s z → s (n z)
_+_ = λ m n → λ s z → m s (n s z)
    = λ m n → λ s → m s ∘ n s
_*_ = λ m n → λ s z → m (n s) z
    = λ m n → λ s → m (n s)
    = λ m n → m ∘ n

_∘_ = λ g f x → g (f x)

lists:
[] = λ i h → h
_∷_ = λ x xs → λ i h → i x (xs i h)

e.g. a ∷ b ∷ [] = λ i h → i a (i b h)

If all lists reduce to normal form, then this implies something about the reduction properties of the arguments (i and h) to a list. We will use _ to stand for no (yet known) constraints on reduction properties, ⋆ to stand for one that reduces to normal form, and t → u for one that is to be given property t and returns u. This may get yet more complicated if we need to consider various reduction properties (head normal, weak head, etc, and then ones that return normal given weak head, or return weak head when given head normal, etc.

[] : (i : _) (h : _) → ⋆
_∷_ : (x : _) (xs : _) (i : _) (h : _) → ⋆

from the definition of [], we must have h : ⋆

[] : (i : _) (h : ⋆) → ⋆
_∷_ : (x : _) (xs : _) (i : _) (h : ⋆) → ⋆

from the definition of _∷_, we must have i : _ → _ → ⋆

[] : (i : _ → _ → ⋆) (h : ⋆) → ⋆
_∷_ : (x : _) (xs : _) (i : _ → _ → ⋆) (h : ⋆) → ⋆

Now, the second argument to i is tied to the return value for xs i h. We will mark it this way. This is like metavariables.

[] : (i : _x → _xs → ⋆) (h : ⋆) → ⋆
_∷_ : (x : _x) (xs : (_x → _xs → ⋆) → ⋆ → _xs) (i : _x → _xs → ⋆) (h : ⋆) → ⋆

But we expect xs must be of the same type as [], so _xs = ⋆

[] : (i : _x → ⋆ → ⋆) (h : ⋆) → ⋆
_∷_ : (x : _x) (xs : (_x → ⋆ → ⋆) → ⋆ → ⋆) (i : _x → ⋆ → ⋆) (h : ⋆) → ⋆

And there we have it: a list of _x.

We could characterise the wanted behavior for lists as that the number of redexes in the output be no greater than in the input? That might get complicated.

head = λ l → l true (error-value-if-list-empty)
tail = λ l → l false ? -- ????
is[] = λ l → l (λ _ _ → false) true

pairs:

_,_ = λ a b → λ f → f a b
fst = λ p → p true
snd = λ p → p false

Ternians

0-ary = λ x _ _ → x
1-ary = λ _ x _ → x
2-ary = λ _ _ x → x
switch_case0_case1_case2_ = λ p x y z → p x y z
is0ary = λ p → switch p case0 true case1 false case2 false

lamda expressions (terms):

var = λ v   → λ lv ll la → lv v
lam = λ t   → λ lv ll la → ll t
app = λ f x → λ lv ll la → la f x

isVar = λ l → l (λ _ → true) (λ _ → false) (λ _ _ → false)
isLam = λ l → l (λ _ → false) (λ _ → true) (λ _ _ → false)
isApp = λ l → l (λ _ → false) (λ _ → false) (λ _ _ → true)
theVar = λ l → l id error error

substitute = λ v t e → λ lv ll la →
               if (isVar t) then (if t ... -- etc. We'll need to be able to compare natural numbers.
               else if (isLam t) then -- now we need to recurse, but how?

To explore recursion, let's try to make a functor map on lists.

map = λ f xs → λ i h → xs (λ x' xs' → i (f x') (map f xs')) h
    = λ f xs i h → xs (λ x' xs' → i (f x') (map f xs')) h
    = λ f xs i h → xs (λ x xs → i (f x) (map f xs)) h
    = λ f xs i h → xs (λ x xs → i (f x) (λ i h → xs (λ x xs → i (f x) (map f xs)) h)) h
    = λ f xs i h → flip xs h (λ x xs → i (f x) (λ i h → flip xs h (λ x xs → i (f x) (map f xs))))

map = λ f l → λ i h → l (λ x xs → i (f x) (map f xs)) h

map = λ f → Y λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h

recmap = λ r f l i h → l (λ x xs → i (f x) (r r f xs)) h
map = recmap recmap
    = (λ f l i h → l (λ x xs → i (f x) ((λ r f l i h → l (λ x xs → i (f x) (r r f xs)) h) (λ r f l i h → l (λ x xs → i (f x) (r r f xs)) h) f xs)) h)


map = λ f → Y λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h

so then

map f [] = (λ f → Y λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h) f []
         = (Y λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h) []
         = (λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h) (Y λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h) []
         = (λ l i h → l (λ x xs → i (f x) ((Y λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h) xs)) h) []
         = λ i h → [] (λ x xs → i (f x) ((Y λ r → λ l i h → l (λ x xs → i (f x) (r xs)) h) xs)) h
         = λ i h → h

so how can we define Y?

want: Y r = r (Y r)

Y = λ r → _1 r

_1 = λ r → _2 r
Y _1 = _1 (Y _1)
(λ r → _1 r) _1 = _1 ((λ r → _1 r) _1)
_1 _1 = _1 ((λ r → _1 r) _1)
(λ r → _1 r) _3 = _3 ((λ r → _1 r) _3)
_1 _3 = _3 (_1 _3)

-- if _3 is a variable, then
_1 = λ r → _5 (r _4)

We need to find some Y such that for any r, Y r = r (Y r). Moreover, we want to find such a Y in the form of an abstraction or variable (i.e., not an application -- why not?)

We want to establish that Y must have the form of an abstraction. There are no variables in context, so Y cannot be a variable. Therefore, it must be an abstraction. (it is still curious why we don't allow for Y to be irreducible to WHNF.)

Thus, wlog, let Y = λ r → y for some y with, possibly r free. Now y is either a variable, an abstraction, or an application.

  case y is a variable

    The only free variable is r, so Y = λ r → r. But then Y r = r and r (Y r) = r r. So we have it that r r = r. But this is not always true, so y is not a variable.

  case y is an abstraction.

    Let y = λ s → z, with r and s free in z. Then Y = λ r s → z, so Y r = λ s → z, and r (Y r) = r (λ s → z). But in case r is a variable, we have it that Y r = λ s → z = λ r s → z. By alpha-equivalence, we have λ s → z = λ r s' → z[s/s']. Applying some variable s to both sides, we have z = λ s' → z[s/s'][r/s]. Substitution of variables for variables does not change the number of abstractions, and clearly the rhs has one more than the left, so y is not an abstraction.

  case y is an application

    let y = f g for some expressions f and g (each, possibly, with r free).

    case f is not reducible to WHNF. Then ?

    case (other cases) ?

    case f and g are in WHNF

      case f is a variable. Then f = r, and Y = λ r → r g, Y r = r g = r (r g). But if r is a variable, there are an inconsistent number of applications here.

      case g is a variable. Then g = r, and Y = λ r → f r, Y r = f = r f. But if r is a variable, we also have inconsistency in number of applications.

      case f is an abstraction


      case f = λ a → b and g = λ c → d

      So, Y = λ r → (λ a → b)(λ c → d)

      Y r = (λ a → b[r/r])(λ c → d[r/r])
          = b[r/r][a/(λ c → d[r/r])]
      r (Y r) = r ((λ a → b[r/r])(λ c → d[r/r]))
              = r b[r/r][a/(λ c → d[r/r])]

      b[r/r][a/(λ c → d[r/r])] = r b[r/r][a/(λ c → d[r/r])]

      Let's rearrange free variables.

      Let f = λ a → b (with a and r free in b)
          g = λ a → c (with a and r free in c)

      Then, Y r = (λ a → b)(λ a → c) --> b[a/λ a → c], so a and r are free in this
        r (Y r) --> r b[a/λ a → c]

      b[a/λ a → c] --> r b[a/λ a → c]

      so b must be an application of r.

      let b = r d, with d having a and r free.

      b[a/λ a → c] = r d[a/λ a → c] <-> d[a/λ a → c]

      Let's try assuming d does not have r free.

      b[a/λ a → c] --> r b[a/λ a → c]

      try

        b = r (a a)
        c = r (a a)

        Then
                  Y r --> b[a/λ a → c]
          b[a/λ a → c] = (λ a → c) (λ a → c)
                       = ((λ a → r (a a)) (λ a → r (a a)))
                       = (r ((λ a → r (a a)) (λ a → r (a a))))


      wait

        we are trying:

          Y = λ r → (λ a → r (a a))(λ a → r (a a))
          Y r = (λ a → r (a a))(λ a → r (a a))
              --> r ((λ a → r (a a))(λ a → r (a a)))
              = r (Y r)






Okay, so we insist that Y is in the form Y = λ r → y and



    again, we want to





In case r is a variable






mapf = λ xs i h →

Okay, i looked it up. We need a Y-combinator.

let's try to invent such a thing from scratch

we want map f xs = R (map f)

if Y r = r (Y r) then we can define
       = r (r (r (r (Y r))))

map = λ f xs → Y (λ i h →

so Y = λ f → ?








Alrighty, so here's a sample program in the language that will actually do something:

primitive
  read -- reads from tape, returns false or true
  write -- writes its argument (should be false or true) to tape
  left -- moves left on the tape
  right -- moves the other way
  bind -- monadic binding

Y = f . (g . g g) (g . f (g g))
zero = f . x . x
one = f . x . f x
suc = n . f . x . f (n f x)
gtZero = ?
pred = ?

true = t . f . t
false = t . f . f
ifthenelse = p . t . f . p t f

sequence = a . b . bind a (_ . b)
main = bind read (v . sequence right (write v))

main-forever = Y (r .
               bind read (v .
               sequence right (
               sequence (write v)
               (r r)
               )))

main-3-times = Y (r . n .
                 ifthenelse (gtZero n)
                            (bind read (v .
                             sequence right (
                             sequence (write v)
                             (r r (pred n))
                             )))
                 (return ?)
                 )
               (suc (suc (suc zero)))


Y = f . (g . g g) (g . f (g g))
  = f . (g . g g f) (g . g g)
zero = f . x . x
one = f . x . x f
suc = n . f . x . (x (f n)) f

















































































-------------------------------------------------------------------------------------------------------

Translating syntax into semantics.

Example: a

Example: comma-separated values (CSV)

Consider the following CSV file (Being somewhat pedantic, <SOF> and <EOF> below indicates the start and end of the file. <LF> and <CR> indicate line-feed and carriage-return control characters).
<SOF>  <LF>
1, ,, alice, "bob"<LF><CR>
2 , "\"Hello, world'" <CR><LF>
"Some long thing  <CR>
 that wraps many, many,<LF>
 lines"<LF>
three , "Goodbye, somewhat abruptly<EOF>

We wish it to be represented by a structure such as the following

<csv-file source-file="  \<NL>1, ,, alice, \"bob\"\<NL>2 , …">
  <csv-row source-row="  " source-row-start=1 source-column-start=1 source-row-end=1 source-column-end=2
           source-end-of-row=LF>
  <csv-row …>
    <csv-column source-column="1"



Here's an interesting adequacy requirement: If we are translating from structure A (say, a `String`) into another structure B (say, an `Int` or `Term` or an `AgdaProgram`)

There are actually three interesting structures:

  The uninterpreted (raw) input
  A set of possible interpretations (for example, "{" might mean


No, let's not get fancy right now.

The thing I want to require is that all interpreted structures are possibly parsed from input. We don't want a situation where it is impossible to get the interpreter to read, say, the string `Hello, "World"` because, say, we forgot to include escape characters for double-quotes and our method for recognising strings in the first place (say, inside a CSV parser) was to look for double-quotes at the start and end.

There are then three structures of interest:

* input
* (i : input) → (j : interpretation) → annotation i j
* interpretation

and the following types

1. (i : input) → decide (∃ (annotation i)) -- if there is no way to annotate the input as an producing any interpretation, we have a proof why that is.
2. (j : interpretation) → ∃ λ i → annotation i j -- there is a possible input for every interpreted structure. This is kind of like (?) that there is at least one possible sent proposition for every possible received proposition.

So the only structure that really needs checking (by human) is the annotation. This makes sense because it represents the "syntax-semantic link".

What about recovery of source code location? That should be possible by further "annotations" within the annotation. So if the input is a string, being interpreted as a row in a CSV file, the annotation

Further complication: we want the human to check that link, but not have to check





annotation → input


So, we might erroneously define CSVString as a quote followed by non-quotes followed by a quote, then have a total parser from String to CSVString.

The interpreted

<see YAF.lagda.md>



```agda
module CSV1 where

  open import Agda.Builtin.String
  Syntax = String

  open import Agda.Builtin.Char
  open import Agda.Builtin.Equality
  data escapeChar : Char → Set where
    escape : escapeChar '\\'
{-
  data escapeString : String → Set where
    escape : {e : Char} → escapeChar e → (c : Char) → escapeString (primListToString (e ∷ c ∷ []))
-}
  isEscapeChar : Char → Set
  isEscapeChar c = c ≡ '\\'

  -- data CSVStringEscapeChar : String
{-
  data CSVStringChar : String → Char → Set where
    escape : ∀ (s : String) → is
    -- normal :
-}
  -- "semantics" of CSV file
  {- i.e. a description of the file adequate for the following uses:
          * reproducing the given file exactly
          * reading-off the primitives
  -}
  {- There is a total function that translates the semantics (interpreted structure) into syntax (in this case, a `String`) and another that does so, vice-versa.
  -}
{-
  data Annotated
    ann : Location

  data CSVString : String → String → Set where
    [] : CSVString "" ""
    _∷c_ :



  data Semantics (input : Syntax) : String → Set where
    eof : (l : Location) → EndOfFile l input →  → Semantics syntax
    row : (List (
    string-value : (s : String)
    numeric-value : (n : Int)
    column-separator :
    row-separator :

  Semantics = List (List (Either
-}

```













































-----------------------------------------------------------------

comment

```agda

open import Data.Empty public using (⊥)
open import Data.Empty using (⊥) renaming (⊥-elim to ⊥-elim) public

```

comment

```agda
data D : Set

data D where
  d : D

data E : Set where
  e : E

open import Agda.Builtin.String

str = "Hello World\"\''{-"

data More : Set where -- <-- that is not part of a comment
str2 = "-}"

```

Reflexive 𝓟 = ∀ x . 𝓟 x x
Symmetric 𝓟 = ∀ x y . 𝓟 x y → 𝓟 y x
Transitive 𝓟 = ∀ x y z . 𝓟 x y ∧ 𝓟 y z → 𝓟 x z
Equivalence 𝓟 = Reflexive 𝓟 ∧ Symmetric 𝓟 ∧ Transitive 𝓟
Irreflexive 𝓟 = ∀ x . ~ 𝓟 x x
Asymmetric 𝓟 = ∀ x y . 𝓟 x y → ~ 𝓟 y x
Trichotomous 𝓟 𝓡 = ∀ x y . 𝓟 x y ∨ 𝓟 y x ↔ ~ 𝓡 x y
Strictorder 𝓟 𝓡 = Irreflexive 𝓟 ∧ Asymmetric 𝓟 ∧ Transitive 𝓟 ∧ Trichotomous 𝓟 𝓡


  Equivalence _=_ ∧ -- equal
  Strictorder _<_ _=_ ∧ -- less-than
  (∀ x y . ~ (x = y) ↔ x ≠ y) ∧ -- not-equal
  (∀ x y . x < y ∨ x = y ↔ x ≤ y) -- less-than-or-equal
  (∃ x . Zero x) ∧ -- there is a number, zero
  (∀ x y . Zero x ∧ Zero y → x = y) ∧ -- and there is "at most one" such number
  (∀ x y . x = y ∧ Zero x → Zero y) ∧ -- Zero respects equality
  (∀ x . Zero x → ∀ y . x ≤ y) ∧ -- zero is at the bottom of the ordering
  (∀ x . x < succ x) ∧ -- numbers are less than their successors
  (∀ x y . x = y → succ x = succ y) ∧ -- succ respects equality
  (∀ x y . succ x = succ y → x = y) ∧ -- there is "at most one" of which something is a successor
  (∀ x y . Zero x → x + y = y) ∧ -- identity for addition
  (∀ x y . succ x + y = succ (x + y)) ∧ -- "induction" for addition
  (∀ w x y z . w = x ∧ y = z → w + y = x + z) ∧ -- addition respects equality
  (∀ x y . Zero x → x * y = x) -- identity for multiplication
  (∀ x y . ~ Zero x → succ x * y = y + (x * y)) ∧ -- "induction" for multiplication
  (∀ x . Zero x → Finite x)
  (∀ x . Finite x → Finite (succ x))
  (∀ x . Finite x)

  -- can we prove that x + y = y + x? Or do we need a principle of induction?

  let's try 0 + y = y + 0
  we have
  0 + y = y
  if y = 0, then we get the solution immediately
  if y = succ y' then we need to be able to assume 0 + y' = y' + 0 and then only need to prove 0 + succ y' = succ y' + 0.
  So, we need:

  (0 + 0 = 0 + 0 ∧ ∀ y → 0 + y = y + 0 → 0 + succ y = succ y + 0) → ∀ y → 0 + y = y + 0 -- a principle of induction

  How about this:
  ∀ x . ~ Zero x → ∃ y . x = succ y ∧ ∀ z .

  -- FOL where the sentences are objects
  (∀ p . True p ⊕ False p)
  (∀ p q . True (conjunction p q) ↔ True p ∧ True q)
  -- but we can't very well model quantification this way!

  -- so how about taking the model to include objects such as
  --   variable symbols, function symbols, predicate symbols, expressions, etc.
  (∀ φ v → IsFormulaWithFreeVariable φ v → (∀ m → ∀ x → x ∈ m → IsTrueIn (substitute φ v x) m) → Valid (universal φ v))
  -- how do we characterise substitute?
  -- that actually might be the easy part: harder is how do we characterise ∈? we need a set theory spelled-out in the background





-- okay, maybe we need to resort to one-to-one functions to clarify that this is modeling something countably infinite?

  (∀ x z . z | x ↔ ∃ y . z = x * y) -- divisibility
  (∀ x y . CD x y ↔ ∃ z . z | x ∧ z | y)
  (∀ x y ∃ z . z = CD x y ↔ ∃ z . z | x ∧ z | y)
  (∀ x y . GCD x y ↔ ) -- greatest common divisor

Better:

define:
  z | x ≡ ∃ y . z = x * y
  CD x y ≡ ∃ z . z | x ∧ z | y
  z ≈ CD x y s.t. P ≡ ∃ z . z | x ∧ z | y ∧ P
  GCD x y ≡ ∃ z . z ≈ CD x y ∧ ∀ w . w ≈ CD x y → w ≤ z

expanded out, what we try to prove in GCD is:

∀ x y ∃ gcd . (∃ x' . x = gcd * x') ∧ (∃ y' . y = gcd * y') ∧ ∀ cd . (∃ x' . x = cd * x') ∧ (∃ y' . y = cd * y') → cd ≤ gcd

If this is provable from the above, then do we have a program for obtaining a gcd?


finite : Nat → Set
finite zero = ⊤
finite (suc n) = finite n

infinite : Nat → Set
infinite n = finite n → ⊥

nothing-is-infinite : ¬ ∃ λ n → infinite n
nothing-is-infinite (zero , inf : (finite zero = ⊤) → ⊥) = inf tt
nothing-is-infinite (suc n , inf : finite n → ⊥) = nothing-is-infinite (n , inf)

Problem is that some statements may be "true" (valid in our favorite model) but not valid. E.g. (∀ z n . (Zero z → P z) ∧ (P n → P (succ n))) → ∀ x . P x



Now say we want to prove

We use the proof (what




Now, let's take some undefined property P and see if induction works. Given (Zero z → P z) ∧ (n' = succ n ∧ P n → P n'), we want to show that P x.

We may reason as follows:
Either x is zero or it's the successor of something. If it's zero, we're done. If it's the successor of something, w, then x = succ w, so we need to show that P w. Either w is zero or it's the successor of something. ...

Suppose ~ P x for some x. If x is zero, then we're in contradiction. So, x is the successor of some w. But then ~ P w. ...

So we can show P 0, and P (succ 0), and P (succ (succ 0)), ... but we cannot show ∀ x P x. Perhaps there could be some P ω we want to rule-out? Where ~ P ω? For example, take P x to mean "x is a finite number of successors after zero". Notice that, in this imagination, ~ P (ω - 1)!

Alright, so maybe we don't care about induction! We're just doing arithmetic after all. Maybe we want to prove that every number divisible by 6 is divisible by 2. Or that there is a greatest common divisor for two numbers. Let's focus on stuff like that that we want to program.

  (∀ x y .






without the last line we could have succ 1 = 3 = succ 2

Do we have it that succ x = succ y → x = y? Suppose x < y.


Do we have it that if Zero x then x < succ y? ... no, we need to say that all numbers are either zero or else the successor of some number

Suppose succ y < x or x = succ y
  Suppose x = succ y


Do we have it that if x < y and y = z then x < z? Either x = z or x < z or z < x. if x = z then x = y, but x < y , so x ≠ y. If z < x then z < y, so z ≠ y, but z = y. So, x < z.

From trichotomy, we have it that ~ (y < z) and ~ (z < y).


Compared to how I can do it in Agda... In Agda I can simply define zero and succ x as the only constructors of numbers, and we get for free that succ x ≠ x.



Equivalence P = ∀ x .

In the metatheory, we regard "=" as a special predicate in that for any model, "x = y" is true iff denotation("x") = denotation("y").

Model-of-Arithmetic

  (∀ x . Number x) ∧ -- everything is a number
  (∀ x . x = x) ∧ -- reflexivity
  (∀ x y . x = y → y = x) ∧ -- symmetry
  (∀ x y z . x = y ∧ y = z → x = z) ∧ -- transitivity
  (∃ x . Zero x) ∧ -- there is a number, zero
  (∀ x y . Zero x ∧ Zero y → x = y) ∧ -- and there is "at most one" such number
  (∀ x y . x = y ∧ Zero x → Zero y) -- Zero respects equality
  (∀ x y . x = y ↔ ~ (x ≠ y)) ∧ -- convenient way of writing inequality
  (∀ x ∃ y . y = succ x ∧ y ≠ x) ∧ -- all numbers have a successor
  (∀ x . Zero x ⊕ ∃ y . x = succ y) ∧ -- all numbers are exactly either zero or the successor of a number (equivalently, zero is the number which is not the successor of any number)
  (∀ x y z . x = y ↔ succ x = succ y) ∧ -- there is "at most one" successor for any given number and for any given successor, there is "at most one" of which it is.
  (∀ x y . Zero x → x + y = y) ∧ -- identity for addition
  (∀ x y . succ x + y = succ (x + y)) -- induction for addition
  (∀ x . Zero x → Finite x)
  (∀ x . Finite x → Finite (succ x))
  (∀ x . Finite x)

Can we conclude from the above that

∀ x . Zero x → succ (succ x) ≠ x -- 2 ≠ 0
yes, b/c if succ (succ x) = x then Zero (succ x) ⊕ ∃ y . succ x = succ y, but we can rule-out Zero (succ x), so succ x = succ y, so x = y ----- err, no

Maybe we need to order all the numbers, so that x < y ∧ y < z → x < z, etc. x < y → x ≠ y, and x < succ x.

Then, we would have
Zero x
x < succ x
succ x < succ (succ x)
x < succ (succ x)
x ≠ succ (succ x)

Let's add some more to try to express finitude.

Can we conclude from the above that (∀ x y . x + y = y → Zero x)?

x + y = y
suppose ~ (Zero x) , for reductio
Zero x ⊕ ∃ y . x = succ y , by UI
∃ y . x = succ y , by ⊕-elim
x = succ x' , by EI
succ x' + y = y , by ?
succ x' + y = succ (x' + y)
y = succ (x' + y)











Hmmm... First order logic, completeness, ?

In FOL, I know from OSCAR that we can decide the validity (truth in all models) of any (wf) formula. So, FOL is complete. Or, better yet Oscar's FOL, (we can call it OFOL) is complete. Arithmetic is "incomplete" in the sense that a certain system (we can call it PM) is incomplete: to be more precise, in PM, every (wf) formula has a truth value (due in part to the fact that the metatheory has a LEM) and yet PM prescribes no method for establishing its truth. This arises in part because it is possible to describe PM's methods and formulas (and certain ways of manipulating formulas) in the language of PM itself.

Questions about OFOL:

* Can we describe OFOL's methods and formulas in OFOL?

We have ∃, ⊗, x₁, f₁, P₁, x₂, f₂, P₂, ... From these we can define (in the metalanguage, so "definitionally")

~ p = p ⊗ p
p ∨ r = ...
... and other logical connectives
∀ x s = ~ ∃ x (~ s)

These are merely meta-language conveniences so that we can write "~ P₁" instead of "P₁ ⊗ P₁".

Is "∀ x (P x) → ∃ x (P x)" valid? After all, it's not true in

We have a notion of a wff.


Okay, let's invent a FOL, call it AFOL, where we include a little more richness. We'll also include a special function, s, and aspecial object, z. We'll also include a special relation, =, for which we will also have that for all x, ~ (x = s x). Validity will be truth in all models (but now we have it that any of those models contain z (and s z and s (s z))).

How will we deal with the function +? Axiomatise x + y = x and x + s y = s (x + y)

We could replace, as above, any object variable with




More straightforwardly? Let's go back to OFOL. We'll "axiomatise" the following conjunction (written in a way where we could translate it into a formula.)

We can state Godel's incompleteness theorem in FOL. The form of the formula will be

Axioms-of-Arithmetic → Incompleteness-of-Arithmetic

The problem is that there's no way (in P → Q) to specify P in such a way as to rule-out finite models for every Q. So how about a different schema? ∃ x (iszero x ∧ ∀ y (y = x ∨ ∃ z (y = suc z)) ∧ ∀ y z (y ≠ suc z) ∧ more-axioms → ?)

The Axioms-of-Arithmetic will be a conjunction that includes such marvels as (∀ x (Number x)), and (∀ x (x = x)), where x will be replaced with x₁, Number for P₁, and = will be handled by P₂. We will not be able to include induction as a schema, because of FOL restrictions. Let's see if we could somehow derive it for any given predicate, P. I imagine:

We want to prove ∀ x (


...

We could have ((∀ x (Number x)) → _) and then all valid formulas under this schema will be those in which

∀ x (IsNumber x → (x = x ∧ ∀ yIsZero x ∨ ∃ y (x Succ y) ∧ Is))

Number = ∀ x (P₁ x)
