
module Oscar.Data.Equality.properties where

open import Relation.Binary.PropositionalEquality public using (cong; cong₂; cong-app; subst; subst₂; sym; trans)

open import Oscar.Data.Equality
open import Oscar.Function
open import Oscar.Level
open import Oscar.Relation

≡̇-refl : ∀ {a} {A : Set a} {b} {B : A → Set b} (f : (x : A) → B x) → f ≡̇ f
≡̇-refl _ _ = refl

≡̇-sym : ∀ {a} {A : Set a} {b} {B : A → Set b} {f g : (x : A) → B x} → f ≡̇ g → g ≡̇ f
≡̇-sym f≡̇g = sym ∘ f≡̇g

≡̇-trans : ∀ {a} {A : Set a} {b} {B : A → Set b} {f g : (x : A) → B x} → f ≡̇ g → {h : (x : A) → B x} → g ⟨ _≡̇ h ⟩→ f
≡̇-trans f≡̇g g≡̇h x = trans (f≡̇g x) (g≡̇h x)

open import Oscar.Category.Setoid

instance

  IsEquivalencePropositionalEquality : ∀ {a} {A : Set a} → IsEquivalence (_≡_ {A = A})
  IsEquivalence.reflexivity IsEquivalencePropositionalEquality _ = refl
  IsEquivalence.symmetry IsEquivalencePropositionalEquality = sym
  IsEquivalence.transitivity IsEquivalencePropositionalEquality = λ ‵ → trans ‵

  IsEquivalenceIndexedPropositionalEquality : ∀ {a} {A : Set a} {b} {B : A → Set b} → IsEquivalence (_≡̇_ {B = B})
  IsEquivalence.reflexivity IsEquivalenceIndexedPropositionalEquality = ≡̇-refl
  IsEquivalence.symmetry IsEquivalenceIndexedPropositionalEquality = ≡̇-sym
  IsEquivalence.transitivity IsEquivalenceIndexedPropositionalEquality = ≡̇-trans

instance

  IsSetoidPropositionalEquality : ∀ {a} {A : Set a} → IsSetoid A a
  IsSetoid._≋_ IsSetoidPropositionalEquality = _≡_

  IsSetoidIndexedPropositionalEquality : ∀ {a} {A : Set a} {b} {B : A → Set b} → IsSetoid ((x : A) → B x) (a ⊔ b)
  IsSetoid._≋_ IsSetoidIndexedPropositionalEquality = _≡̇_

setoidPropositionalEquality : ∀ {a} (A : Set a) → Setoid a a
Setoid.⋆ (setoidPropositionalEquality A) = A

setoidIndexedPropositionalEquality : ∀ {a} {A : Set a} {b} (B : A → Set b) → Setoid (a ⊔ b) (a ⊔ b)
Setoid.⋆ (setoidIndexedPropositionalEquality {A = A} B) = (x : A) → B x
Setoid.isSetoid (setoidIndexedPropositionalEquality B) = IsSetoidIndexedPropositionalEquality {B = B}

open import Oscar.Category.Action

actionΣ : ∀ {a} {A : Set a} {b} (B : A → Set b) → Action A b b
Action.𝔄 (actionΣ B) x = setoidPropositionalEquality (B x)

_⇒_ : ∀ {a} (A : Set a) {b} (B : Set b) → Setoid _ _
_⇒_ A B = setoidIndexedPropositionalEquality {A = A} λ _ → B

open import Oscar.Category.Semigroupoid
open import Oscar.Category.Morphism

⇧ : ∀ {a} {A : Set a} {b} (B : A → A → Set b) → Morphism A b b
Morphism._⇒_ (⇧ B) x y = setoidPropositionalEquality (B x y)
IsSetoid._≋_ (Morphism.isSetoid (⇧ B)) = _≡_

_⇨_ : ∀ {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) → Morphism A (b ⊔ c) (b ⊔ c)
Morphism._⇒_ (B ⇨ C) = λ m n → B m ⇒ C n
IsSetoid._≋_ (Morphism.isSetoid (B ⇨ C)) = _≡̇_

IsSemigroupoid⋆ : ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : A → Set c}
                    (let _↦_ = λ m n → B m → C n)
                    (_∙_ : ∀ {y z} → y ↦ z → ∀ {x} → x ↦ y → x ↦ z) → Set (lsuc (a ⊔ b ⊔ c))
IsSemigroupoid⋆ _∙_ = IsSemigroupoid (_ ⇨ _) _∙_

Semigroupoid⋆ :
  ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : A → Set c}
                    (let _↦_ = λ m n → B m → C n)
                    (_∙_ : ∀ {y z} → y ↦ z → ∀ {x} → x ↦ y → x ↦ z)
    ⦃ _ : IsSemigroupoid⋆ _∙_ ⦄
    → Semigroupoid _ _ _
Semigroupoid⋆ _∙_ = _ ⇨ _ , _∙_

open import Oscar.Category.Semigroupoid

instance

  isSemigroupoidFunctions≡̇ : ∀ {a} {A : Set a} {b} {B : A → Set b} → IsSemigroupoid (B ⇨ B) (λ g f → g ∘ f)
  IsSemigroupoid.extensionality isSemigroupoidFunctions≡̇ {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)
  IsSemigroupoid.associativity isSemigroupoidFunctions≡̇ _ _ _ _ = refl

semigroupoidFunction : ∀ {a} {A : Set a} {b} (B : A → Set b) → Semigroupoid _ _ _
semigroupoidFunction B = B ⇨ B , (λ ‵ → _∘_ ‵)

open import Oscar.Category.Category

instance

  isCategoryFunctions≡̇ : ∀ {a} {A : Set a} {b} {B : A → Set b} → IsCategory (semigroupoidFunction B) id
  IsCategory.left-identity isCategoryFunctions≡̇ _ _ = refl
  IsCategory.right-identity isCategoryFunctions≡̇ _ _ = refl

categoryFunction : ∀ {a} {A : Set a} {b} (B : A → Set b) → Category _ _ _
categoryFunction B = semigroupoidFunction B , id



-- -- open import Oscar.Property.Reflexivity

-- -- instance Reflexivity≡ : ∀ {a} {A : Set a} → Reflexivity (_≡_ {A = A})
-- -- Reflexivity.reflexivity Reflexivity≡ _ = refl

-- -- instance Reflexivity≡̇ : ∀ {a} {A : Set a} {b} {B : A → Set b} → Reflexivity (_≡̇_ {B = B})
-- -- Reflexivity.reflexivity Reflexivity≡̇ _ _ = refl

-- -- open import Oscar.Property.Symmetry

-- -- instance Symmetry≡ : ∀ {a} {A : Set a} → Symmetry (_≡_ {A = A})
-- -- Symmetry.symmetry Symmetry≡ = sym

-- -- instance Symmetry≡̇ : ∀ {a} {A : Set a} {b} {B : A → Set b} → Symmetry (_≡̇_ {B = B})
-- -- Symmetry.symmetry Symmetry≡̇ = ≡̇-sym

-- -- open import Oscar.Property.Transitivity

-- -- instance Transitivity≡ : ∀ {a} {A : Set a} → Transitivity (_≡_ {A = A})
-- -- Transitivity.transitivity Transitivity≡ x≡y = trans x≡y

-- -- instance Transitivity≡̇ : ∀ {a} {A : Set a} {b} {B : A → Set b} → Transitivity (_≡̇_ {B = B})
-- -- Transitivity.transitivity Transitivity≡̇ = ≡̇-trans

-- -- -- {-
-- -- -- _∘₂_ : ∀ {a b c}
-- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- --         (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
-- -- --         ((x : A) → C (g x))
-- -- -- f ∘₂ g = λ x → f (g x)
-- -- -- -}


-- -- -- open import Oscar.Class.Equivalence

-- -- -- instance ReflexivityPropositional : ∀ {a} {A : Set a} → Reflexivity (_≡_ {A = A})
-- -- -- Reflexivity.reflexivity ReflexivityPropositional = refl

-- -- -- instance SymmetryPropositional : ∀ {a} {A : Set a} → Symmetry (_≡_ {A = A})
-- -- -- Symmetry.symmetry SymmetryPropositional = sym

-- -- -- instance TransitivityPropositional : ∀ {a} {A : Set a} → Transitivity (_≡_ {A = A})
-- -- -- Transitivity.transitivity TransitivityPropositional = trans

-- -- -- open import Prelude using (it)

-- -- -- instance Equivalence⋆ : ∀ {a} {A : Set a} {ℓ} {_≋_ : A → A → Set ℓ} ⦃ _ : Reflexivity _≋_ ⦄ ⦃ _ : Symmetry _≋_ ⦄ ⦃ _ : Transitivity _≋_ ⦄ → Equivalence _≋_
-- -- -- Equivalence.reflexivityI Equivalence⋆ = it
-- -- -- Equivalence.symmetryI Equivalence⋆ = it
-- -- -- Equivalence.transitivityI Equivalence⋆ = it

-- -- -- -- -- {-
-- -- -- -- -- instance EquivalencePropositional : ∀ {a} {A : Set a} → Equivalence (_≡_ {A = A})
-- -- -- -- -- Equivalence.reflexivity EquivalencePropositional = refl
-- -- -- -- -- Equivalence.symmetry EquivalencePropositional = sym
-- -- -- -- -- Equivalence.transitivity EquivalencePropositional = trans

-- -- -- -- -- instance EquivalencePointwise : ∀ {a} {A : Set a} {b} {B : A → Set b} → Equivalence (_≡̇_ {B = B})
-- -- -- -- -- Equivalence.reflexivity EquivalencePointwise x = refl
-- -- -- -- -- Equivalence.symmetry EquivalencePointwise = ≡̇-sym
-- -- -- -- -- Equivalence.transitivity EquivalencePointwise = ≡̇-trans
-- -- -- -- -- -}

-- -- -- instance CongruousEquivalencesPropositional : ∀ {a} {A : Set a} {b} {B : Set b} → CongruousEquivalences (_≡_ {A = A}) (_≡_ {A = B})
-- -- -- CongruousEquivalences.equivalence₁ CongruousEquivalencesPropositional = it
-- -- -- CongruousEquivalences.equivalence₂ CongruousEquivalencesPropositional = it
-- -- -- CongruousEquivalences.congruity CongruousEquivalencesPropositional = cong

-- -- -- postulate
-- -- --   FunctionName : Set

-- -- -- open import Oscar.Data.Nat
-- -- -- open import Oscar.Data.Fin
-- -- -- open import Oscar.Data.Term FunctionName
-- -- -- open import Oscar.Data.Term.Injectivity FunctionName

-- -- -- instance InjectiveEquivalencesTermI : ∀ {m : Nat} → InjectiveEquivalences (_≡_ {A = Fin m}) (_≡_ {A = Term m}) Term.i Term.i
-- -- -- InjectiveEquivalences.equivalence₁ InjectiveEquivalencesTermI = it
-- -- -- InjectiveEquivalences.equivalence₂ InjectiveEquivalencesTermI = it
-- -- -- InjectiveEquivalences.injectivity InjectiveEquivalencesTermI refl = reflexivity

-- -- -- instance InjectiveEquivalencesTermLeft : ∀ {m : Nat} {r₁ r₂ : Term m} → InjectiveEquivalences _≡_ _≡_ (_fork r₁) (_fork r₂)
-- -- -- InjectiveEquivalences.equivalence₁ InjectiveEquivalencesTermLeft = it
-- -- -- InjectiveEquivalences.equivalence₂ InjectiveEquivalencesTermLeft = it
-- -- -- InjectiveEquivalences.injectivity InjectiveEquivalencesTermLeft refl = reflexivity

-- -- -- instance InjectiveEquivalencesTermRight : ∀ {m : Nat} {l₁ l₂ : Term m} → InjectiveEquivalences _≡_ _≡_ (l₁ fork_) (l₂ fork_)
-- -- -- InjectiveEquivalences.equivalence₁ InjectiveEquivalencesTermRight = it
-- -- -- InjectiveEquivalences.equivalence₂ InjectiveEquivalencesTermRight = it
-- -- -- InjectiveEquivalences.injectivity InjectiveEquivalencesTermRight refl = reflexivity

-- -- -- injectivity' :
-- -- --   ∀ {a} {A : Set a} {ℓ₁} {_≋₁_ : A → A → Set ℓ₁}
-- -- --     {b} {B : Set b}
-- -- --     {f : A → B}
-- -- --     {g : A → B}
-- -- --     ⦃ _ : InjectiveEquivalences _≋₁_ _≡_ f g ⦄ →
-- -- --   ∀ {x y} → f x ≡ g y → x ≋₁ y
-- -- -- injectivity' x = injectivity {_≋₂_ = _≡_} x

-- -- -- Term-forkLeft-inj' : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → l₁ ≡ l₂
-- -- -- Term-forkLeft-inj' {n} {l₁} {r₁} {l₂} {r₂} x = injectivity' x
-- -- -- --Term-forkLeft-inj' {n} {l₁} {r₁} {l₂} {r₂} x = injectivity {_≋₂_ = _≡_} x
-- -- -- -- injectivity {_≋₁_ = {!_≡_!}} {_≋₂_ = {!_≡_!}} ⦃ InjectiveEquivalencesTermLeft ⦄ x

-- -- -- Term-forkRight-inj' : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → r₁ ≡ r₂
-- -- -- Term-forkRight-inj' {n} {l₁} {r₁} {l₂} {r₂} x = injectivity' x
-- -- -- --Term-forkLeft-inj' {n} {l₁} {r₁} {l₂} {r₂} x = injectivity {_≋₂_ = _≡_} x
-- -- -- -- injectivity {_≋₁_ = {!_≡_!}} {_≋₂_ = {!_≡_!}} ⦃ InjectiveEquivalencesTermLeft ⦄ x
