
module Match-RefineBug where

module Level where

  open import Agda.Primitive public

module Bool where

  open import Agda.Builtin.Bool public

module List where

  open import Agda.Builtin.List public

module Nat where

  open import Agda.Builtin.Nat public

module Equality where

  open import Agda.Builtin.Equality public

module Empty where

  data ⊥ : Set where

  infix -1 ¬_
  ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
  ¬ x = x → ⊥

module Decidable where

  open Empty

  data Decidable {ℓ} (A : Set ℓ) : Set ℓ where
    yes : A → Decidable A
    no : ¬ A → Decidable A

module Product where

  open Level

  infixr 5 _,_
  data Σ {ℓa} (A : Set ℓa) {ℓb} (B : A → Set ℓb) : Set (ℓa ⊔ ℓb) where
    _,_ : (x : A) → B x → Σ A B

  ∃ : ∀ {ℓa} {A : Set ℓa} {ℓb} (B : A → Set ℓb) → Set (ℓa ⊔ ℓb)
  ∃ = Σ _

  infixr 5 _×_
  _×_ : ∀ {ℓa} (A : Set ℓa) {ℓb} (B : Set ℓb) → Set (ℓa ⊔ ℓb)
  A × B = Σ A (λ _ → B)

  car : ∀ {ℓa} {A : Set ℓa} {ℓb} {B : A → Set ℓb} → Σ A B → A
  car (a , _) = a

  cdr : ∀ {ℓa} {A : Set ℓa} {ℓb} {B : A → Set ℓb} → (product : Σ A B) → B (car product)
  cdr (_ , b) = b

module ListFunctor where

  open List

  _<$>_ : ∀ {ℓa} {A : Set ℓa} {ℓb} {B : Set ℓb} → (A → B) → List A → List B
  _<$>_ f [] = []
  _<$>_ f (x ∷ xs) = f x ∷ (f <$> xs)

module ListMembership where

  open List
  open Empty
  open Decidable
  open Equality

  it : ∀ {a} {A : Set a} ⦃ _ : A ⦄ → A
  it ⦃ x ⦄ = x

  data _∈_ {ℓ} {A : Set ℓ} (a : A) : List A → Set ℓ where
    instance
      here : ∀ as → a ∈ (a ∷ as)
      there : ∀ {as} → a ∈ as → ∀ x → a ∈ (x ∷ as)

  _∉_ : ∀ {ℓ} {A : Set ℓ} → A → List A → Set ℓ
  a ∉ as = ¬ a ∈ as

  list : ∀ {ℓ} {A : Set ℓ} {a : A} {xs : List A} → a ∈ xs → List A
  list {xs = xs} _ = xs

  element : ∀ {ℓ} {A : Set ℓ} {a : A} {xs : List A} → a ∈ xs → A
  element {a = a} _ = a

  _∈?_ : ∀ {ℓ} {A : Set ℓ} ⦃ eq? : {x : A} → {y : A} → Decidable (x ≡ y) ⦄ (a : A) (xs : List A) → Decidable (a ∈ xs)
  a ∈? [] = no λ ()
  _∈?_ ⦃ eq? ⦄ a (x ∷ xs) with eq? {a} {x}
  ... | yes a≡x rewrite a≡x = yes (here _)
  ... | no a≢x with a ∈? xs
  ... | yes a∈xs = yes (there a∈xs _)
  ... | no a∉xs = no λ { (here _) → a≢x it ; (there a∈xs _) → a∉xs a∈xs }

module AssociationList where

  open Level
  open Product
  open List
  open ListMembership
  open ListFunctor

  infixl 1 _∷_↦_
  data AssociationList {ℓk} (K : Set ℓk) {ℓv} (V : K → Set ℓv) : List (Σ K V) → Set (ℓk ⊔ ℓv) where
    [] : AssociationList K V []
    _∷_↦_
      : {kvs : List (Σ K V)} (map : AssociationList K V kvs)
        {k : K} (k∉kvs : k ∉ (car <$> kvs)) → (v : V k) → AssociationList K V ((k , v) ∷ kvs)

  get : ∀ {ℓk} {K : Set ℓk} {ℓv} {V : K → Set ℓv} {kvs : List (Σ K V)} {k : K} → (associationList : AssociationList K V kvs) → k ∈ (car <$> kvs) → V k
  get = {!!}

module ListProperties where

  open List
  open Nat

  length : ∀ {ℓ} {A : Set ℓ} → List A → Nat
  length [] = zero
  length (_ ∷ as) = suc (length as)

module ⟦Map⟧-stuff where

  open Level

  open Equality
  open Nat
  open List
  open Product

  open ListProperties
  open AssociationList

  Carrier : ∀ {ℓk} (K : Set ℓk) {ℓv} (V : K → Set ℓv) → List (Σ K V) → Nat → Set (ℓk ⊔ ℓv)
  Carrier K V ls n = length ls ≡ n → AssociationList K V ls

module Freer where

  open Level

  data Freer {ℓa ℓb} (F : Set ℓa → Set ℓb) (A : Set ℓa) : Set (lsuc (ℓa ⊔ ℓb)) where
    purer : A → Freer F A
    freer : ∀ {𝑎 : Set ℓa} → (𝑎 → Freer F A) → F 𝑎 → Freer F A

module Formula where

  open Level
  open Freer
  open List

  Formula : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
  Formula A = Freer List A

module FormulaMembership where

  open Level
  open List
  open Freer
  open Formula

  data _∈_ {ℓ} {A : Set ℓ} (a : A) : Formula A → Set (lsuc ℓ) where
    here : a ∈ purer a
    there : ∀ {𝑎 : Set ℓ} {f : 𝑎 → Formula A} {x : 𝑎} → a ∈ f x → a ∈ freer f (x ∷ [])
    somewhere : ∀ {𝑎 : Set ℓ} {f : 𝑎 → Formula A} {xs : List 𝑎} → (x : 𝑎) → a ∈ freer f xs → a ∈ freer f (x ∷ xs)

module Schema where

  open Level
  open Bool
  open Product
  open Formula

  Schema : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
  Schema A = Formula A × (A → Bool)

  schema-formula : ∀ {ℓ} {A : Set ℓ} → Schema A → Formula A
  schema-formula schema = car schema

  schema-isVariable : ∀ {ℓ} {A : Set ℓ} → Schema A → A → Bool
  schema-isVariable schema = cdr schema

module Overlay where

  open Level
  open Freer
  open Formula
  open Schema
  open Product
  open Bool
  open Equality
  open List

  data _⋐_ {ℓ} {A : Set ℓ} : Schema A → Formula A → Set (lsuc ℓ) where
    var : (x : A) (isVariable : A → Bool) (formula : Formula A) ( _ : isVariable x ≡ true ) → ((purer x , isVariable) ⋐ formula)
    const : (x : A) (isVariable : A → Bool) (formula : Formula A) ⦃ _ : isVariable x ≡ false ⦄ → ((purer x , isVariable) ⋐ purer x)
    freer[] : (isVariable : A → Bool) (𝑎 : Set ℓ) (f : 𝑎 → Freer List A) (𝑏 : Set ℓ) (g : 𝑏 → Freer List A) → (freer f [] , isVariable) ⋐ freer g []
    freer∷ : (isVariable : A → Bool) (𝑎 : Set ℓ) (f : 𝑎 → Freer List A) (𝑏 : Set ℓ) (g : 𝑏 → Freer List A)
             (x : 𝑎) (y : 𝑏) (xs : List 𝑎) (ys : List 𝑏) →
             (f x , isVariable) ⋐ g y →
             (freer f xs , isVariable) ⋐ freer g ys →
             (freer f (x ∷ xs) , isVariable) ⋐ freer g (y ∷ ys)

module OverlayMembership where

  open Level
  open Freer
  open Formula
  open Schema
  open Product
  open Bool
  open Equality
  open List
  open Overlay

  data _∈_ {ℓ} {A : Set ℓ} (x : A) : {schema : Schema A} {formula : Formula A} → (schema ⋐ formula) → Set (lsuc ℓ) where
    var : (isVariable : A → Bool) (formula : Formula A) → ( eq : isVariable x ≡ true ) → x ∈ {!!}
--var x isVariable formula eq
