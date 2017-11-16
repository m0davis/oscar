
module Oscar.Data.Substitist {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Fin
open import Oscar.Data.Nat
open import Oscar.Data.Product
open import Oscar.Data.Term FunctionName
open import Oscar.Data.AList
open import Oscar.Data.Equality

Substitist : Nat → Nat → Set 𝔣
Substitist m n = AList (λ m → Term m × Fin (suc m)) n m

pattern anil = []
pattern _asnoc_/_ σ t x = (t , x) ∷ σ

_⊸_ = Substitist

infixr 9 _∙_
_∙_ : ∀ {m n} → m ⊸ n → ∀ {l} → l ⊸ m → l ⊸ n
ρ ∙ anil = ρ
ρ ∙ (σ asnoc t / x) = (ρ ∙ σ) asnoc t / x

∙-associativity : ∀ {k l} (f : k ⊸ l) {m} (g : l ⊸ m) {n} (h : m ⊸ n) → (h ∙ g) ∙ f ≡ h ∙ g ∙ f
∙-associativity anil σ _ = refl
∙-associativity (τ asnoc t / x) ρ σ = cong (λ s → s asnoc t / x) (∙-associativity τ ρ σ)

ε : ∀ {n} → n ⊸ n
ε = anil

∙-left-identity : ∀ {m n} (σ : m ⊸ n) → ε ∙ σ ≡ σ
∙-left-identity anil = refl
∙-left-identity (σ asnoc t' / x) = cong (λ σ → σ asnoc t' / x) (∙-left-identity σ)

∙-right-identity : ∀ {m n} (σ : m ⊸ n) → σ ∙ ε ≡ σ
∙-right-identity _ = refl

open import Oscar.Category

semigroupoidSubstitist : Semigroupoid Substitist (λ {x y} → ≡-setoid (Substitist x y))
Semigroupoid._∙_ semigroupoidSubstitist = _∙_
Semigroupoid.∙-extensionality semigroupoidSubstitist refl refl = refl
Semigroupoid.∙-associativity semigroupoidSubstitist = ∙-associativity

Substitist' : Nat → Nat → Set 𝔣
Substitist' m n = AList (λ m → Term m × Fin (suc m)) m n

semigroupoidSubstitist' : Semigroupoid Substitist' (λ {x y} → ≡-setoid (Substitist' x y))
semigroupoidSubstitist' = Category'.semigroupoidAList

categorySubstitist : Category semigroupoidSubstitist
Category.ε categorySubstitist = ε
Category.ε-left-identity categorySubstitist = ∙-left-identity _
Category.ε-right-identity categorySubstitist = ∙-right-identity _
