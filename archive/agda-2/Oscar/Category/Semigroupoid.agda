
module Oscar.Category.Semigroupoid where

open import Oscar.Data.Equality
open import Oscar.Level
open import Oscar.Relation

record Semigroupoid
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔪} (_⊸_ : 𝔒 → 𝔒 → Ø 𝔪)
  : Ø 𝔬 ∙̂ 𝔪 where
  infixr 9 _∙_
  field
    _∙_ : ∀ {m n} → m ⊸ n → ∀ {l} → l ⊸ m → l ⊸ n
    ∙-associativity : ∀ {k l} (f : k ⊸ l) {m} (g : l ⊸ m) {n} (h : m ⊸ n) → (h ∙ g) ∙ f ≡ h ∙ g ∙ f

record Category
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔪} (_⊸_ : 𝔒 → 𝔒 → Ø 𝔪)
  : Ø 𝔬 ∙̂ 𝔪 where
  field
    semigroupoid : Semigroupoid _⊸_
  open Semigroupoid semigroupoid public

  field
    ε : ∀ {n} → n ⊸ n
    ε-left-identity : ∀ {m n} (σ : m ⊸ n) → ε ∙ σ ≡ σ
    ε-right-identity : ∀ {m n} (σ : m ⊸ n) → σ ∙ ε ≡ σ

record RCategory
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔪} {_⊸_ : 𝔒 → 𝔒 → Ø 𝔪}
  (category : Category _⊸_)
  : Ø 𝔬 ∙̂ 𝔪 where
  open Category category public hiding (semigroupoid)

module MCategory
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔪} {_⊸_ : 𝔒 → 𝔒 → Ø 𝔪}
  (category : Category _⊸_)
  where
  open Category category public hiding (semigroupoid)


-- open import Oscar.Category.Morphism
-- open import Oscar.Category.Setoid
-- open import Oscar.Level
-- open import Oscar.Relation

-- module _ {𝔬} {𝔪} {𝔮} (𝔐 : Morphism 𝔬 𝔪 𝔮) (open Morphism 𝔐) where
--   record IsSemigroupoid (_∙_ : Transitive _↦_) : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮)) where
--     field
--       extensionality : Extensional _∙_ _≞_
--       associativity : Associative _∙_ _≞_

-- open IsSemigroupoid ⦃ … ⦄ public

-- infixr 4 _,_
-- record Semigroupoid 𝔬 𝔪 𝔮 : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮))
--   where
--   constructor _,_

--   field
--     𝔐 : Morphism 𝔬 𝔪 𝔮

--   open Morphism 𝔐 public

--   infixl 7 _∙_
--   field _∙_ : Transitive _↦_

--   field ⦃ isSemigroupoid ⦄ : IsSemigroupoid 𝔐 _∙_
--   open IsSemigroupoid isSemigroupoid public
