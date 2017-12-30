
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Term.Layer0.Mutual.Sandbox where

open import Type.Prelude
```

```agda
open import Type.Term.Layer0.Mutual
open import Type.Complexity
open import Type.Term.Layer-1.SCTerm
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
