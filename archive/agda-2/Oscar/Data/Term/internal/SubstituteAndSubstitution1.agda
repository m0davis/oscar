
module Oscar.Data.Term.internal.SubstituteAndSubstitution1 {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Equality
open import Oscar.Data.Equality.properties
open import Oscar.Data.Fin
open import Oscar.Data.Nat
open import Oscar.Data.Term FunctionName
open import Oscar.Data.Vec
open import Oscar.Function

infix 19 _◃_ _◃s_
mutual

  _◃_ : ∀ {m n} → (f : m ⊸ n) → Term m → Term n
  σ̇ ◃ i 𝑥 = σ̇ 𝑥
  _ ◃ leaf = leaf
  σ̇ ◃ (τl fork τr) = (σ̇ ◃ τl) fork (σ̇ ◃ τr)
  σ̇ ◃ (function fn τs) = function fn (σ̇ ◃s τs) where

  _◃s_ : ∀ {m n} → m ⊸ n → ∀ {N} → Vec (Term m) N → Vec (Term n) N
  f ◃s [] = []
  f ◃s (t ∷ ts) = f ◃ t ∷ f ◃s ts

_◇_ : ∀ {m n} → m ⊸ n → ∀ {l} → l ⊸ m → l ⊸ n
_◇_ f g = (f ◃_) ∘ g

mutual

  ◃-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → f ◃_ ≡̇ g ◃_
  ◃-extensionality p (i x) = p x
  ◃-extensionality p leaf = refl
  ◃-extensionality p (s fork t) = cong₂ _fork_ (◃-extensionality p s) (◃-extensionality p t)
  ◃-extensionality p (function fn ts) = cong (function fn) (◃s-extensionality p ts)

  ◃s-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → ∀ {N} → _◃s_ f {N} ≡̇ _◃s_ g
  ◃s-extensionality p [] = refl
  ◃s-extensionality p (t ∷ ts) = cong₂ _∷_ (◃-extensionality p t) (◃s-extensionality p ts)

mutual

  ◃-associativity : ∀ {l m} (f : l ⊸ m) {n} (g : m ⊸ n) → (g ◇ f) ◃_ ≡̇ (g ◃_) ∘ (f ◃_)
  ◃-associativity _ _ (i _) = refl
  ◃-associativity _ _ leaf = refl
  ◃-associativity _ _ (τ₁ fork τ₂) = cong₂ _fork_ (◃-associativity _ _ τ₁) (◃-associativity _ _ τ₂)
  ◃-associativity f g (function fn ts) = cong (function fn) (◃s-associativity f g ts)

  ◃s-associativity : ∀ {l m n} (f : l ⊸ m) (g : m ⊸ n) → ∀ {N} → (_◃s_ (g ◇ f) {N}) ≡̇ (g ◃s_) ∘ (f ◃s_)
  ◃s-associativity _ _ [] = refl
  ◃s-associativity _ _ (τ ∷ τs) = cong₂ _∷_ (◃-associativity _ _ τ) (◃s-associativity _ _ τs)

◇-associativity : ∀ {k l} (f : k ⊸ l) {m} (g : l ⊸ m) {n} (h : m ⊸ n) → (h ◇ g) ◇ f ≡̇ h ◇ (g ◇ f)
◇-associativity f g h x rewrite ◃-associativity g h (f x) = refl

◇-extensionality : ∀ {l m} {f₁ f₂ : l ⊸ m} → f₁ ≡̇ f₂ → ∀ {n} {g₁ g₂ : m ⊸ n} → g₁ ≡̇ g₂ → g₁ ◇ f₁ ≡̇ g₂ ◇ f₂
◇-extensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = ◃-extensionality g₁≡̇g₂ (f₂ x)

open import Oscar.Category.Semigroupoid

SemigroupoidSubstitution : Semigroupoid _ _ _
Semigroupoid.⋆ SemigroupoidSubstitution = _
Semigroupoid._⇒_ SemigroupoidSubstitution m n = Fin m ⇒ Term n
Semigroupoid._∙_ SemigroupoidSubstitution = _◇_
Semigroupoid.associativity SemigroupoidSubstitution = ◇-associativity
Semigroupoid.extensionality SemigroupoidSubstitution = ◇-extensionality

open import Oscar.Category.Semifunctor

SemifunctorSubstitution : Semifunctor _ _ _ _ _ _
Semifunctor.semigroupoid₁ SemifunctorSubstitution = SemigroupoidSubstitution
Semifunctor.semigroupoid₂ SemifunctorSubstitution = SemigroupoidFunction Term
Semifunctor.μ SemifunctorSubstitution = id
Semifunctor.𝔣 SemifunctorSubstitution = _◃_
Semifunctor.extensionality SemifunctorSubstitution = ◃-extensionality
Semifunctor.preservativity SemifunctorSubstitution = ◃-associativity

ε : ∀ {m} → m ⊸ m
ε = i

mutual

  ◃-identity : ∀ {m} (t : Term m) → ε ◃ t ≡ t
  ◃-identity (i x) = refl
  ◃-identity leaf = refl
  ◃-identity (s fork t) = cong₂ _fork_ (◃-identity s) (◃-identity t)
  ◃-identity (function fn ts) = cong (function fn) (◃s-identity ts)

  ◃s-identity : ∀ {N m} (t : Vec (Term m) N) → ε ◃s t ≡ t
  ◃s-identity [] = refl
  ◃s-identity (t ∷ ts) = cong₂ _∷_ (◃-identity t) (◃s-identity ts)

◇-left-identity : ∀ {m n} (f : m ⊸ n) → ε ◇ f ≡̇ f
◇-left-identity f = ◃-identity ∘ f

◇-right-identity : ∀ {m n} (f : m ⊸ n) → f ◇ ε ≡̇ f
◇-right-identity _ _ = refl

open import Oscar.Category.Category

CategorySubstitution : Category _ _ _
Category.semigroupoid CategorySubstitution = SemigroupoidSubstitution
Category.ε CategorySubstitution = ε
Category.left-identity CategorySubstitution = {!!}
Category.right-identity CategorySubstitution {x} {y} {f} x₁ = ◇-right-identity f x₁

test-right-id = {!Category.right-identity CategorySubstitution!}

-- open import Oscar.Property.Associativity
-- open import Oscar.Property.Equivalence
-- open import Oscar.Property.Extensionality₂

-- instance

--   AssociativitySubstitutionComposition : Associativity _◇_ _≡̇_
--   Associativity.associativity AssociativitySubstitutionComposition = ◇-associativity

--   ExtensionalityS◇ : ExtensionalitySemigroupoid _◇_ _≡̇_
--   ExtensionalitySemigroupoid.extensionalitySemigroupoid ExtensionalityS◇ g₁≡̇g₂ {_} {_} {f₂} f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ◃-extensionality g₁≡̇g₂ (f₂ x)

-- -- instance

-- --   Extensionality₂≡̇◇⋆ : ∀ {x y z} → Extensionality₂⋆ _≡̇_ _≡̇_ (λ ‵ → _≡̇_ ‵) ((y ⊸ z → x ⊸ y → x ⊸ z) ∋ λ ` → _◇_ `) (λ ` → _◇_ `)
-- --   Extensionality₂⋆.extensionality* Extensionality₂≡̇◇⋆ g₁≡̇g₂ {_} {f₂} f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ◃-extensionality g₁≡̇g₂ (f₂ x)

-- -- --  Extensionality₂≡̇◇ : ∀ {x y z} → Extensionality₂ _≡̇_ _≡̇_ (λ ‵ → _≡̇_ ‵) (λ {yz} → _◇_ {y} {z} yz {x}) (λ {_} {yz} → yz ◇_)
-- -- --  Extensionality₂.extensionality₂ Extensionality₂≡̇◇ {g₁} {g₂} g₁≡̇g₂ {f₁} {f₂} f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ◃-extensionality g₁≡̇g₂ (f₂ x)

-- instance

--   SemigroupoidSubstitution : Semigroupoid _ _ _
--   Semigroupoid.⋆ SemigroupoidSubstitution = _
--   Semigroupoid._⇒_ SemigroupoidSubstitution = _⊸_
--   Semigroupoid._≋_ SemigroupoidSubstitution = _≡̇_
--   Semigroupoid._∙_ SemigroupoidSubstitution = _◇_

-- instance

--   Associativity-∘ : ∀ {𝔬} {⋆ : Set 𝔬} {f} {F : ⋆ → Set f} →
--                     Associativity (λ {y} {z} g {x} f₁ x₁ → g (f₁ x₁))
--                                   (λ {x} {y} f₁ g → (x₁ : F x) → f₁ x₁ ≡ g x₁)
--   Associativity.associativity Associativity-∘ _ _ _ _ = refl

--   ExtensionalityS∘ : ∀ {𝔬} {⋆ : Set 𝔬} {f} {F : ⋆ → Set f} → ExtensionalitySemigroupoid (λ g f → {!(λ {_} → g) ∘ f!}) (_≡̇_ {B = F})
--   ExtensionalityS∘ = {!!}


-- --   Extensionality₂-≡̇ : ∀ {𝔬} {⋆ : Set 𝔬} {f} {F : ⋆ → Set f} {x y z : ⋆} →
-- --      Extensionality₂ {_} {F _ → _} {_} {λ _ → F _ → _}
-- --      (λ f₁ g → (x₁ : F y) → _≡_ (f₁ x₁) (g x₁)) {_}
-- --      {λ {w} _ → F _ → _} {_} {λ {w} {x₁} _ → F x → F y} {f}
-- --      (λ {w} {x₁} f₁ g → (x₂ : F x) → _≡_ {f} {F y} (f₁ x₂) (g x₂)) {f}
-- --      {λ {w} {y₁} _ → F x → F z} {f} {λ {w} {x₁} {y₁} _ → F x → F z} {f}
-- --      (λ {w} {x₁} {y₁} ′ {z₁} g →
-- --         (x₂ : F x) → _≡_ (′ x₂) (g x₂))
-- --      (λ {yz} f₁ x₂ → yz (f₁ x₂))
-- --      (λ {_} {yz} f₁ x₁ → yz (f₁ x₁))
-- --   Extensionality₂.extensionality₂ Extensionality₂-≡̇ w≡̇x y≡̇z f rewrite y≡̇z f = w≡̇x _


-- SemigroupoidIndexedFunction : ∀ {𝔬} {⋆ : Set 𝔬} {f} (F : ⋆ → Set f) → Semigroupoid _ _ _
-- Semigroupoid.⋆ (SemigroupoidIndexedFunction F) = _
-- Semigroupoid._⇒_ (SemigroupoidIndexedFunction F) m n = F m → F n
-- Semigroupoid._≋_ (SemigroupoidIndexedFunction F) = _≡̇_
-- Semigroupoid._∙_ (SemigroupoidIndexedFunction F) g f = g ∘ f
-- Semigroupoid.′associativity (SemigroupoidIndexedFunction F) = it
-- Semigroupoid.′extensionality₂ (SemigroupoidIndexedFunction F) = {!!} -- Extensionality₂-≡̇ {F = F}

-- open import Oscar.Property.Extensionality

-- instance

--   ex : ∀ {x y} →
--        Extensionality (λ f g →
--                          (x₁ : Fin x) →
--                          _≡_ (f x₁) (g x₁))
--        (λ {x₁} ‵ {y₁} g →
--           (x₂ : Term x) →
--           _≡_ {𝔣} {Term y} (‵ x₂) (g x₂))
--        _◃_ _◃_
--   Extensionality.extensionality ex = ◃-extensionality

-- open import Oscar.Property.Preservativity

-- instance

--   pres : ∀ {x y z} →
--          Preservativity {𝔣}
--          {Fin y → Term z} {𝔣}
--          {λ _ → Fin x → Term y} {𝔣}
--          {λ x₁ _ → Fin x → Term z}
--          (λ ‵ g x₁ → _◃_ {y} {z} ‵ (g x₁)) {𝔣}
--          {Term y →
--           Term z}
--          {𝔣}
--          {λ _ →
--             Term x →
--             Term y}
--          {𝔣}
--          {λ x₁ _ →
--             Term x →
--             Term z}
--          (λ ‵ f x₁ → ‵ (f x₁)) {𝔣}
--          (λ {x₁} {y₁} f g →
--             (x₂ : Term x) →
--             _≡_ {𝔣} {Term z} (f x₂) (g x₂))
--          (_◃_ {y} {z}) (λ {x₁} → _◃_ {x} {y}) (λ {x₁} {y₁} → _◃_ {x} {z})
--   Preservativity.preservativity pres ρ₂ ρ₁ t = ◃-associativity' t ρ₁ ρ₂

-- semifunctor : Semifunctor _ _ _ _ _ _
-- Semifunctor.semigroupoid₁ semifunctor = SemigroupoidSubstitution
-- Semifunctor.semigroupoid₂ semifunctor = SemigroupoidIndexedFunction Term
-- Semifunctor.μ semifunctor = id
-- Semifunctor.𝔣 semifunctor = _◃_
