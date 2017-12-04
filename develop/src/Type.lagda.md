
# Type theory, metaprogrammed (eventually)

```agda
module Type where
```

I develop a partial (or maybe a full) implementation of a particular type theory and then turn back to re-develop it as an instance of a general (metaprogrammed) type theory.

```agda
open import Prelude
open import Type.Common
```

My first attempt at implementing a type theory was to represent that from the HoTT book, Appendix 2. I added a notion of complexity on the idea that it would help in proving that type inference (finding a term that witnesses a given type) is semi-decidable (that eventually, in some sense, any type capable of being witnessed will in fact be witnessed). I ran into trouble with cumbersome substitutions of DeBruijn-indexed variables.

```agda
import Type.First as F
```

An idea to streamline the process was to use a mutually-defined weakening function for terms.

```agda
import Type.Mutual as M
```

Then another idea was to come-up with a method for referring to variables by their names.

```agda
import Type.Named as N
```

While trying to define a type-checked notion of substitution of a variable defined in one context for a term in a different (but, somehow, compatible) context, I discovered that representing type membership in a linear context would require representing the dependency structure. This is unlike in STLC, where a type can be identified by its encoding. In a dependent type, the encoding of the same type may be different, depending on the postitions of the types depended upon in the context. This reminded me of the tree-like structure of an argument from several premises to a conclusion.

```agda
import Type.Argument as A
```

`Argument` was just getting started when I went back to `Named` with the idea I might have a fix. While working on that, I thought that it would be helpful to prove that one can apply term instantiation and weakening in different orders and produce equal results. However, when I tried to prove this, I found it quite cumbersome and was reminded of the McBride's advisement against "green slime" in "How to Keep Your Neighbours in Order". I realised then that I had a more fundamental problem.

```agda
import Type.Slimeless as S
```

```agda
𝟎 𝟏 𝟐 𝟑 𝟒 : ∀ {N} → Term N
𝟎 = ℕIZ
𝟏 = ℕIS 𝟎
𝟐 = ℕIS 𝟏
𝟑 = ℕIS 𝟐
𝟒 = ℕIS 𝟑

-- add x represents a function that adds x to a given input
add : ∀ {N} → Term N → Term N
add x = ℕE (ΠF ℕF ℕF) -- form a function f : ℕ → ℕ
           -- case x = ℕIZ
           -- λ y → y
           (ΠI (𝓋 zero))
           -- case x = ℕIS x₋₁
           -- λ x₋₁ f →
              -- λ y → suc (f y)
              (ΠI (ℕIS (ΠE (𝓋 (suc zero)) (𝓋 zero))))
           x

_+ℕ_ : ∀ {N} → Term N → Term N → Term N
x +ℕ y = ΠE (add x) y

double : ∀ {N} → Term N → Term N
double x = ΠE (ΠI (add (𝓋 zero))) x

multiply : ∀ {N} → Term N → Term N
multiply x = ℕE (ΠF ℕF ℕF)
                (ΠI ℕIZ)
                (ΠI let x₋₁ = 𝓋 (suc (suc zero)) ; f = 𝓋 (suc zero) ; y = 𝓋 zero in
                    y +ℕ (ΠE f x₋₁))
                x

_*ℕ_ : ∀ {N} → Term N → Term N → Term N
x *ℕ y = ΠE (multiply x) y

_=ℕ_ : ∀ {N} → Term N → Term N → Term N
x =ℕ y = =F ℕF x y
```

## test drive(s)

```
module Sandbox-F where
  open F

  check-𝟙→𝟙 : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F ⋖ c (c [] ∷ c [] ∷ [])
  check-𝟙→𝟙 = ΠI zero 𝟙F (Vble refl)

  infer-𝟙→𝟙 : [] ⊢ ΠF 𝟙F 𝟙F
  infer-𝟙→𝟙 = ΠI (𝓋 zero) , c (c [] ∷ c [] ∷ []) , ΠI zero 𝟙F (Vble refl)

  check-𝟎=𝟎 : [] ⊢ =I 𝟎 ∶ (𝟎 =ℕ 𝟎)
  check-𝟎=𝟎 = c (c [] ∷ c [] ∷ []) , =I zero ℕF ℕIZ

  infer-𝟎+𝟎=𝟎 : [] ⊢ (𝟎 =ℕ 𝟎)
  infer-𝟎+𝟎=𝟎 = =I ℕIZ , c (c [] ∷ c [] ∷ []) , =I zero ℕF ℕIZ

  check-𝟎+𝟏=𝟏 : [] ⊢ =I 𝟏 ∶ ((𝟎 +ℕ 𝟏) =ℕ 𝟏)
  check-𝟎+𝟏=𝟏 = {!!} , {!!}

  infer-∀n→doublen=𝟐*n : [] ⊢ ΠF ℕF
                                 let n = 𝓋 zero in (double n =ℕ (𝟐 *ℕ n))
  infer-∀n→doublen=𝟐*n = ΠI (=I (𝓋 zero)) , {!!} , {!!}

  check-upsetting : [] ⊢ ℕIS 𝟙I ∶ ℕF
  check-upsetting = {!!} , {!!}
```

```
module Sandbox-M where
  open M

  check-𝟙→𝟙 : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F ⋖ c (c [] ∷ c [] ∷ [])
  check-𝟙→𝟙 = ΠI zero 𝟙F (Vble refl)

  infer-𝟙→𝟙 : [] ⊢ ΠF 𝟙F 𝟙F
  infer-𝟙→𝟙 = ΠI (𝓋 zero) , c (c [] ∷ c [] ∷ []) , ΠI zero 𝟙F (Vble refl)

  check-𝟎=𝟎 : [] ⊢ =I 𝟎 ∶ (𝟎 =ℕ 𝟎)
  check-𝟎=𝟎 = c (c [] ∷ c [] ∷ []) , =I zero ℕF ℕIZ

  infer-𝟎+𝟎=𝟎 : [] ⊢ (𝟎 =ℕ 𝟎)
  infer-𝟎+𝟎=𝟎 = =I ℕIZ , c (c [] ∷ c [] ∷ []) , =I zero ℕF ℕIZ

  check-𝟎+𝟏=𝟏 : [] ⊢ =I 𝟏 ∶ ((𝟎 +ℕ 𝟏) =ℕ 𝟏)
  check-𝟎+𝟏=𝟏 = {!!} , {!!}

  infer-∀n→doublen=𝟐*n : [] ⊢ ΠF ℕF
                                 let n = 𝓋 zero in (double n =ℕ (𝟐 *ℕ n))
  infer-∀n→doublen=𝟐*n = ΠI (=I (𝓋 zero)) , {!!} , {!!}

  check-upsetting : [] ⊢ ℕIS 𝟙I ∶ ℕF
  check-upsetting = {!!} , {!!}
```

```
module Sandbox-N where
  open N
  check-𝟙→𝟙 : ε ⊢ ΠF 𝟙F 𝟙F ∋ ΠI (𝓋 zero)
  check-𝟙→𝟙 = {!!}

  infer-𝟙→𝟙 : ε ⊢ ΠF 𝟙F 𝟙F
  infer-𝟙→𝟙 = {!!}

  {- commented-out until I develop the API
  check-𝟎=𝟎 : [] ⊢ =I 𝟎 ∶ (𝟎 =ℕ 𝟎)
  check-𝟎=𝟎 = c (c [] ∷ c [] ∷ []) , =I zero ℕF ℕIZ

  infer-𝟎+𝟎=𝟎 : [] ⊢ (𝟎 =ℕ 𝟎)
  infer-𝟎+𝟎=𝟎 = =I ℕIZ , c (c [] ∷ c [] ∷ []) , =I zero ℕF ℕIZ

  check-𝟎+𝟏=𝟏 : [] ⊢ =I 𝟏 ∶ ((𝟎 +ℕ 𝟏) =ℕ 𝟏)
  check-𝟎+𝟏=𝟏 = {!!} , {!!}

  infer-∀n→doublen=𝟐*n : [] ⊢ ΠF ℕF
                                 let n = 𝓋 zero in (double n =ℕ (𝟐 *ℕ n))
  infer-∀n→doublen=𝟐*n = ΠI (=I (𝓋 zero)) , {!!} , {!!}

  check-upsetting : [] ⊢ ℕIS 𝟙I ∶ ℕF
  check-upsetting = {!!} , {!!}
  -}
```

```
module Sandbox-A where
  open A
```

```
module Sandbox-S where
  open S
```
