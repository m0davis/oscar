
module Oscar.Data.Term.internal.SubstituteAndSubstitution {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Category.Action
open import Oscar.Category.Category
open import Oscar.Category.CategoryAction
open import Oscar.Category.Functor
open import Oscar.Category.Morphism
open import Oscar.Category.Semifunctor
open import Oscar.Category.Semigroupoid
open import Oscar.Category.Setoid
open import Oscar.Category.SemigroupoidAction
open import Oscar.Data.Equality
open import Oscar.Data.Equality.properties
open import Oscar.Data.Fin
open import Oscar.Data.Nat
open import Oscar.Data.Term FunctionName
open import Oscar.Data.Vec
open import Oscar.Function
open import Oscar.Level
open import Oscar.Relation

𝕞₁ : Morphism _ _ _
𝕞₁ = Fin ⇨ Term

𝕞₂ : Morphism _ _ _
𝕞₂ = Term ⇨ Term

𝕞₂ₛ : Nat → Morphism _ _ _
𝕞₂ₛ N = Terms N ⇨ Terms N

module 𝔐₁ = Morphism 𝕞₁
module 𝔐₂ = Morphism 𝕞₂
module 𝔐₂ₛ (N : Nat) where open Morphism (𝕞₂ₛ N) public using () renaming (_↦_ to _[_↦_])

private

  infix 19 _◂_ _◂s_

  mutual

    _◂_ : ∀ {m n} → m 𝔐₁.↦ n → m 𝔐₂.↦ n
    σ̇ ◂ i 𝑥 = σ̇ 𝑥
    _ ◂ leaf = leaf
    σ̇ ◂ (τl fork τr) = (σ̇ ◂ τl) fork (σ̇ ◂ τr)
    σ̇ ◂ (function fn τs) = function fn (σ̇ ◂s τs) where

    _◂s_ : ∀ {m n} → m ⊸ n → ∀ {N} → N 𝔐₂ₛ.[ m ↦ n ] -- Vec (Term m) N → Vec (Term n) N
    f ◂s [] = []
    f ◂s (t ∷ ts) = f ◂ t ∷ f ◂s ts

  _∙_ : ∀ {m n} → m ⊸ n → ∀ {l} → l ⊸ m → l ⊸ n
  _∙_ f g = (f ◂_) ∘ g

  mutual

    ◂-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → f ◂_ ≡̇ g ◂_
    ◂-extensionality p (i x) = p x
    ◂-extensionality p leaf = refl
    ◂-extensionality p (s fork t) = cong₂ _fork_ (◂-extensionality p s) (◂-extensionality p t)
    ◂-extensionality p (function fn ts) = cong (function fn) (◂s-extensionality p ts)

    ◂s-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → ∀ {N} → _◂s_ f {N} ≡̇ _◂s_ g
    ◂s-extensionality p [] = refl
    ◂s-extensionality p (t ∷ ts) = cong₂ _∷_ (◂-extensionality p t) (◂s-extensionality p ts)

  mutual

    ◂-associativity : ∀ {l m} (f : l ⊸ m) {n} (g : m ⊸ n) → (g ∙ f) ◂_ ≡̇ (g ◂_) ∘ (f ◂_)
    ◂-associativity _ _ (i _) = refl
    ◂-associativity _ _ leaf = refl
    ◂-associativity _ _ (τ₁ fork τ₂) = cong₂ _fork_ (◂-associativity _ _ τ₁) (◂-associativity _ _ τ₂)
    ◂-associativity f g (function fn ts) = cong (function fn) (◂s-associativity f g ts)

    ◂s-associativity : ∀ {l m n} (f : l ⊸ m) (g : m ⊸ n) → ∀ {N} → (_◂s_ (g ∙ f) {N}) ≡̇ (g ◂s_) ∘ (f ◂s_)
    ◂s-associativity _ _ [] = refl
    ◂s-associativity _ _ (τ ∷ τs) = cong₂ _∷_ (◂-associativity _ _ τ) (◂s-associativity _ _ τs)

  ∙-associativity : ∀ {k l} (f : k ⊸ l) {m} (g : l ⊸ m) {n} (h : m ⊸ n) → (h ∙ g) ∙ f ≡̇ h ∙ (g ∙ f)
  ∙-associativity f g h x rewrite ◂-associativity g h (f x) = refl

  ∙-extensionality : ∀ {l m} {f₁ f₂ : l ⊸ m} → f₁ ≡̇ f₂ → ∀ {n} {g₁ g₂ : m ⊸ n} → g₁ ≡̇ g₂ → g₁ ∙ f₁ ≡̇ g₂ ∙ f₂
  ∙-extensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = ◂-extensionality g₁≡̇g₂ (f₂ x)

instance

  IsSemigroupoid𝕞₁∙ : IsSemigroupoid 𝕞₁ _∙_
  IsSemigroupoid.extensionality IsSemigroupoid𝕞₁∙ = ∙-extensionality
  IsSemigroupoid.associativity IsSemigroupoid𝕞₁∙ = ∙-associativity

𝕘₁ : Semigroupoid _ _ _
𝕘₁ = 𝕞₁ , _∙_

𝕘₂ : Semigroupoid _ _ _
𝕘₂ = 𝕞₂ , (λ ‵ → _∘_ ‵)

𝕘₂ₛ : Nat → Semigroupoid _ _ _
𝕘₂ₛ N = 𝕞₂ₛ N , (λ ‵ → _∘_ ‵)

𝕘₁,₂ : Semigroupoids _ _ _ _ _ _
𝕘₁,₂ = 𝕘₁ , 𝕘₂

instance

  IsSemifunctor𝕘₁₂◂ : IsSemifunctor 𝕘₁,₂ _◂_
  IsSemifunctor.extensionality IsSemifunctor𝕘₁₂◂ = ◂-extensionality
  IsSemifunctor.distributivity IsSemifunctor𝕘₁₂◂ = ◂-associativity

𝕗◂ : Semifunctor _ _ _ _ _ _
𝕗◂ = 𝕘₁,₂ , _◂_

𝕘₁,₂ₛ : Nat → Semigroupoids _ _ _ _ _ _
𝕘₁,₂ₛ N = 𝕘₁ , 𝕘₂ₛ N

instance

  IsSemifunctor𝕘₁,₂ₛ◂s : ∀ {N} → IsSemifunctor (𝕘₁,₂ₛ N) (λ ‵ → _◂s_ ‵)
  IsSemifunctor.extensionality IsSemifunctor𝕘₁,₂ₛ◂s f≡̇g τs = ◂s-extensionality f≡̇g τs
  IsSemifunctor.distributivity IsSemifunctor𝕘₁,₂ₛ◂s f g x = ◂s-associativity f g x

𝕗◂s : Nat → Semifunctor _ _ _ _ _ _
𝕗◂s N = 𝕘₁,₂ₛ N , (λ ‵ → _◂s_ ‵)

𝕒₂ : Action _ _ _
𝕒₂ = actionΣ Term

𝕒₂ₛ : Nat → Action _ _ _
𝕒₂ₛ N = actionΣ (Terms N)

instance

  IsSemigroupoidAction𝕘₁𝕒₂◂ : IsSemigroupoidAction 𝕘₁ 𝕒₂ _◂_
  IsSemigroupoidAction.extensionality IsSemigroupoidAction𝕘₁𝕒₂◂ {s₁ = s₁} refl f₁≡̇f₂ = ◂-extensionality f₁≡̇f₂ s₁
  IsSemigroupoidAction.associativity IsSemigroupoidAction𝕘₁𝕒₂◂ s f g = ◂-associativity f g s

  IsSemigroupoidAction𝕘₁𝕒₂ₛ◂s : ∀ {N} → IsSemigroupoidAction 𝕘₁ (𝕒₂ₛ N) (λ ‵ → _◂s_ ‵)
  IsSemigroupoidAction.extensionality IsSemigroupoidAction𝕘₁𝕒₂ₛ◂s {s₁ = s₁} refl f₁≡̇f₂ = ◂s-extensionality f₁≡̇f₂ s₁
  IsSemigroupoidAction.associativity IsSemigroupoidAction𝕘₁𝕒₂ₛ◂s s f g = ◂s-associativity f g s

𝕟◂ : SemigroupoidAction _ _ _ _ _
𝕟◂ = [ 𝕘₁ / 𝕒₂ ] _◂_

𝕟◂s : Nat → SemigroupoidAction _ _ _ _ _
𝕟◂s N = [ 𝕘₁ / 𝕒₂ₛ N ] (λ ‵ → _◂s_ ‵)

private

  ε : ∀ {m} → m ⊸ m
  ε = i

  mutual

    ◂-identity : ∀ {m} (t : Term m) → ε ◂ t ≡ t
    ◂-identity (i x) = refl
    ◂-identity leaf = refl
    ◂-identity (s fork t) = cong₂ _fork_ (◂-identity s) (◂-identity t)
    ◂-identity (function fn ts) = cong (function fn) (◂s-identity ts)

    ◂s-identity : ∀ {N m} (t : Vec (Term m) N) → ε ◂s t ≡ t
    ◂s-identity [] = refl
    ◂s-identity (t ∷ ts) = cong₂ _∷_ (◂-identity t) (◂s-identity ts)

  ∙-left-identity : ∀ {m n} (f : m ⊸ n) → ε ∙ f ≡̇ f
  ∙-left-identity f = ◂-identity ∘ f

  ∙-right-identity : ∀ {m n} (f : m ⊸ n) → f ∙ ε ≡̇ f
  ∙-right-identity _ _ = refl

instance

  IsCategory𝕘₁ε : IsCategory 𝕘₁ ε
  IsCategory.left-identity IsCategory𝕘₁ε = ∙-left-identity
  IsCategory.right-identity IsCategory𝕘₁ε = ∙-right-identity

𝔾₁ : Category _ _ _
𝔾₁ = 𝕘₁ , ε

𝔾₂ : Category _ _ _
𝔾₂ = 𝕘₂ , id

𝔾₂ₛ : Nat → Category _ _ _
𝔾₂ₛ N = 𝕘₂ₛ N , id

𝔾₁,₂ : Categories _ _ _ _ _ _
𝔾₁,₂ = 𝔾₁ , 𝔾₂

𝔾₁,₂ₛ : Nat → Categories _ _ _ _ _ _
𝔾₁,₂ₛ N = 𝔾₁ , 𝔾₂ₛ N

instance

  IsFunctor𝔾₁,₂◂ : IsFunctor 𝔾₁,₂ _◂_
  IsFunctor.identity IsFunctor𝔾₁,₂◂ _ = ◂-identity

𝔽◂ : Functor _ _ _ _ _ _
𝔽◂ = 𝔾₁,₂ , _◂_

instance

  IsFunctor𝔾₁,₂ₛ◂ : ∀ {N} → IsFunctor (𝔾₁,₂ₛ N) (λ ‵ → _◂s_ ‵)
  IsFunctor.identity IsFunctor𝔾₁,₂ₛ◂ _ = ◂s-identity -- ◂-identity

𝔽s : Nat → Functor _ _ _ _ _ _
𝔽s N = 𝔾₁,₂ₛ N , (λ ‵ → _◂s_ ‵)

instance

  IsCategoryAction𝔾₁𝕒₂◂ : IsCategoryAction 𝔾₁ 𝕒₂ _◂_
  IsCategoryAction.identity IsCategoryAction𝔾₁𝕒₂◂ = ◂-identity

  IsCategoryAction𝔾₁𝕒₂ₛ◂s : ∀ {N} → IsCategoryAction 𝔾₁ (𝕒₂ₛ N) (λ ‵ → _◂s_ ‵)
  IsCategoryAction.identity IsCategoryAction𝔾₁𝕒₂ₛ◂s = ◂s-identity

ℕ◂ : CategoryAction _ _ _ _ _
ℕ◂ = [ 𝔾₁ / 𝕒₂ ] _◂_

ℕ◂s : Nat → CategoryAction _ _ _ _ _
ℕ◂s N = [ 𝔾₁ / 𝕒₂ₛ N ] (λ ‵ → _◂s_ ‵)
