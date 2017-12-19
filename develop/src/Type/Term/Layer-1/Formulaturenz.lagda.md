
```agda
-- {-# OPTIONS --allow-unsolved-metas #-}
```

Disallowing empty signature.

```agda
module Type.Term.Layer-1.Formulaturenz where
```

```agda
open import Type.Prelude
```

```agda
open import Type.Term.Layer-2.DeBruijn

Universe = Nat
data Formula (N : Nat) : Set
data Signature (N : Nat) : ∀ {M} → Vec Nat (suc M) → Set
data Formula (N : Nat) where
  𝒰 : Universe → Formula N
  𝓋 : Fin N → Formula N
  ΠF : Signature N (0 ∷ 1 ∷ []) → Formula N
  ΠI : Signature N (0 ∷ 1 ∷ []) → Formula N
  ΠE : Signature N (0 ∷ 0 ∷ []) → Formula N
  ΣF : Signature N (0 ∷ 1 ∷ []) → Formula N
  ΣI : Signature N (0 ∷ 0 ∷ []) → Formula N
  ΣE : Signature N (1 ∷ 2 ∷ 0 ∷ []) → Formula N
  +F : Signature N (0 ∷ 0 ∷ []) → Formula N
  +Iˡ : Signature N (0 ∷ []) → Formula N
  +Iʳ : Signature N (0 ∷ []) → Formula N
  +E : Signature N (1 ∷ 1 ∷ 1 ∷ 0 ∷ []) → Formula N
  𝟘F : Formula N
  𝟘E : Signature N (1 ∷ 0 ∷ []) → Formula N
  𝟙F : Formula N
  𝟙I : Formula N
  𝟙E : Signature N (1 ∷ 0 ∷ 0 ∷ []) → Formula N
  ℕF : Formula N
  ℕIᶻ : Formula N
  ℕIˢ : Signature N (0 ∷ []) → Formula N
  ℕE : Signature N (1 ∷ 0 ∷ 2 ∷ 0 ∷ []) → Formula N
  =F : Signature N (0 ∷ 0 ∷ 0 ∷ []) → Formula N
  =I : Signature N (0 ∷ []) → Formula N
  =E : Signature N (3 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []) → Formula N
data Signature (N : Nat) where
  ⟨_⟩ : ∀ {v} → Formula (v + N) → Signature N (v ∷ [])
  _∷_ : ∀ {v} → Formula (v + N)
      → ∀ {M} {vs : Vec Nat (suc M)} → Signature N vs
      → Signature N (v ∷ vs)
```

```agda
testFormula₁ : Formula 0
testFormula₁ = ΠF (𝒰 0 ∷ ⟨ 𝓋 0 ⟩)
```
