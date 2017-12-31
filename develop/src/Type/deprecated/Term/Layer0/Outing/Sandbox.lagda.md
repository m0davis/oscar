
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.deprecated.Term.Layer0.Outing.Sandbox where

open import Type.Prelude
```

```agda
open import Type.deprecated.Term.Layer0.Outing
open import Type.deprecated.Term.Layer0.Outing.Admissible
open import Type.deprecated.Term.Layer+1.Context
open import Type.deprecated.Term.Layer+1.Formula
open DefinedFunctions

check-𝟙→𝟙 : ε ⊢ ΠI 𝟙F (zero ↦₁ 𝓋 zero) ∶ ΠF 𝟙F (zero ↦₁ 𝟙F)
check-𝟙→𝟙 = ΠI (var (ctx-EXT {ℓ = zero} (𝟙F ctx-EMP) unit) zero refl refl)

infer-𝟙→𝟙 : ε ⊨ ΠF 𝟙F (zero ↦₁ 𝟙F)
infer-𝟙→𝟙 = ⟨ ΠI 𝟙F (zero ↦₁ 𝓋 zero) ∶ ΠI (var (ctx-EXT {ℓ = zero} (𝟙F ctx-EMP) unit) zero refl refl) ⟩

check-𝟎=𝟎 : ε ⊢ =I 𝟎 ∶ 𝟎 =ℕ 𝟎
check-𝟎=𝟎 = =I (ℕIᶻ ctx-EMP)

infer-𝟎+𝟎=𝟎 : ε ⊨ 𝟎 +ℕ 𝟎 =ℕ 𝟎
infer-𝟎+𝟎=𝟎 = ⟨ {!!} ∶ {!!} ⟩

infer-∀n→doublen=𝟐*n : ε ⊨ ΠF ℕF
                              (let n = 0 in
                                n ↦₁ double (𝓋 n) =ℕ 𝟐 *ℕ (𝓋 n))
infer-∀n→doublen=𝟐*n = {!!}

check-not-upsetting : ε ⊢ ℕIˢ 𝟙I ∶ ℕF → ⊥
check-not-upsetting = {!!}
```
