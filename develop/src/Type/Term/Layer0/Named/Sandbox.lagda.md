
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Term.Layer0.Named.Sandbox where

open import Type.Prelude
```

```
open import Type.Term.Layer0.Named
open import Type.Term.Layer-1.SCTerm
open DefinedFunctions

check-𝟙→𝟙 : ε ⊢ ΠF 𝟙F 𝟙F ∋ ΠI (𝓋 zero)
check-𝟙→𝟙 = {!!}

infer-𝟙→𝟙 : ε ⊢ ΠF 𝟙F 𝟙F
infer-𝟙→𝟙 = {!!}

check-𝟎=𝟎 : ε ⊢ 𝟎 =ℕ 𝟎 ∋ =I 𝟎
check-𝟎=𝟎 = {!!}

infer-𝟎+𝟎=𝟎 : ε ⊢ (𝟎 =ℕ 𝟎)
infer-𝟎+𝟎=𝟎 = {!!}

check-𝟎+𝟏=𝟏 : ε ⊢ ((𝟎 +ℕ 𝟏) =ℕ 𝟏) ∋ =I 𝟏
check-𝟎+𝟏=𝟏 = {!!}

infer-∀n→doublen=𝟐*n : ε ⊢ ΠF ℕF
                               let n = 𝓋 zero in (double n =ℕ (𝟐 *ℕ n))
infer-∀n→doublen=𝟐*n = {!!}

check-upsetting : ε ⊢ ℕF ∋ ℕIS 𝟙I
check-upsetting = {!!}
```
