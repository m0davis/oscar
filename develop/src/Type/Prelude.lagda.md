
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Prelude where
```

```agda
open import Prelude public
```

I will repurpose _,_.

```agda
  renaming
    (_,_ to _,,_)
```

```agda
open import Tactic.Nat public
```

## some conveniences that are here, inconveniently

```agda
∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃_ = Σ _
```

```agda
_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
a ≢ b = ¬ (a ≡ b)
```

```agda
max≥₁ : (a b : Nat) → max a b ≥ a
max≥₁ = {!!}

max≥₂ : (a b : Nat) → max a b ≥ b
max≥₂ = {!!}
```
