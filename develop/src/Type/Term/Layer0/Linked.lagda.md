
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Term.Layer0.Linked where
```

```agda
open import Type.Prelude
open import Type.Term.Layer+1.Formula -- named terms
open import Type.Term.Layer-1.SCTerm  -- DeBruijn-indexed terms
open import Type.Term.Layer+1.Context -- context of named terms
open import Type.Term.Layer+2.Variable -- named variables
```

Conversion from a named term in a context to its DeBruijn representation. I will take it that names in the prefix of a context may shadow names in its suffix, just as abstractions shadow the names they bind. I will not accomodate the case that a variable in a named term has a referent that is not in the context or in an enclosing abstraction.

```agda
_⊆_ : Formula → Context → Set
φ ⊆ Γ = ∀ v → v ∈ φ → v ∈ Γ

inj-⊆-ΠF₁ : ∀ {Γ A φ} → ΠF A φ ⊆ Γ → A ⊆ Γ
inj-⊆-ΠF₁ {ε} ΠFAB⊆Γ v v∈A v∉Γ = ΠFAB⊆Γ v {!!} {!!}
inj-⊆-ΠF₁ {Γ , x ∶ _} ΠFAB⊆Γ v v∈A v∉Γ = {!!}

toDeBruijn : (Γ : Context) → (φ : Formula) → (φ ⊆ Γ) → Term (lengthContext Γ)
toDeBruijn Γ (𝒰 ℓ) φ⊆Γ = 𝒰 {!ℓ!}
toDeBruijn Γ (𝓋 x) φ⊆Γ = {!φ⊆Γ x!}
toDeBruijn Γ (ΠF A (x ↦₁ B)) φ⊆Γ = ΠF (toDeBruijn Γ A (inj-⊆-ΠF₁ {Γ = Γ} {A = A} {φ = x ↦₁ B} φ⊆Γ)) (toDeBruijn (Γ , {!!} ∶ A) B {!!})
toDeBruijn Γ (ΠI φ x) φ⊆Γ = {!!}
toDeBruijn Γ (ΠE φ φ₁) φ⊆Γ = {!!}
toDeBruijn Γ (ΣF φ x) φ⊆Γ = {!!}
toDeBruijn Γ (ΣI φ φ₁) φ⊆Γ = {!!}
toDeBruijn Γ (ΣE x x₁ φ) φ⊆Γ = {!!}
toDeBruijn Γ (+F φ φ₁) φ⊆Γ = {!!}
toDeBruijn Γ (+Iˡ φ) φ⊆Γ = {!!}
toDeBruijn Γ (+Iʳ φ) φ⊆Γ = {!!}
toDeBruijn Γ (+E x x₁ x₂ φ) φ⊆Γ = {!!}
toDeBruijn Γ 𝟘F φ⊆Γ = {!!}
toDeBruijn Γ (𝟘E x φ) φ⊆Γ = {!!}
toDeBruijn Γ 𝟙F φ⊆Γ = {!!}
toDeBruijn Γ 𝟙I φ⊆Γ = {!!}
toDeBruijn Γ (𝟙E x φ φ₁) φ⊆Γ = {!!}
toDeBruijn Γ ℕF φ⊆Γ = {!!}
toDeBruijn Γ ℕIᶻ φ⊆Γ = {!!}
toDeBruijn Γ (ℕIˢ φ) φ⊆Γ = {!!}
toDeBruijn Γ (ℕE (z ↦₁ C) cᶻ cˢ n) φ⊆Γ = ℕE (toDeBruijn (Γ , z ∶ ℕF) C {!!}) {!!} {!!} {!!}
toDeBruijn Γ (=F φ φ₁ φ₂) φ⊆Γ = {!!}
toDeBruijn Γ (=I φ) φ⊆Γ = {!!}
toDeBruijn Γ (=E x x₁ φ φ₁ φ₂) φ⊆Γ = {!!}
```
