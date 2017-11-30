
# Type theory, metaprogrammed (eventually)

```agda
module Type where
```

I develop a partial (or maybe a full) implementation of a particular type theory and then turn back to re-develop it as an instance of a general (metaprogrammed) type theory.

```agda
open import Prelude
open import Type.Common
import Type.First as F
import Type.Mutual as M
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
