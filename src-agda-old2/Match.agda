
module Match where

module Level where

  open import Agda.Primitive public

module Bool where

  open import Agda.Builtin.Bool public

  data IsTrue : Bool → Set where
    instance true : IsTrue true

  data IsFalse : Bool → Set where
    instance false : IsFalse false

module List where

  open import Agda.Builtin.List public

module Nat where

  open import Agda.Builtin.Nat public

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

module Equality where

  open import Agda.Builtin.Equality public

  open Decidable

  record Equality {ℓ} (A : Set ℓ) : Set ℓ where
    field
      _≟_ : (x : A) → (y : A) → Decidable (x ≡ y)

  open Equality ⦃ ... ⦄ public

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

module Sum where

  data Orientation : Set where
    left right : Orientation

  record Boolean (A : Set) : Set where
    inductive
    field
      negative-value : A
      positive-value : A

  open Boolean ⦃ ... ⦄

  open Bool
  instance
    BoolBoolean : Boolean Bool
    BoolBoolean = record { negative-value = false ; positive-value = true }

    OrientationBoolean : Boolean Orientation
    OrientationBoolean = record { negative-value = left ; positive-value = right }

  open Level
  open Equality

  record _⊎_ {ℓˡ ℓʳ} (L : Set ℓˡ) (R : Set ℓʳ) : Set (ℓˡ ⊔ ℓʳ) where
    field
      orientation : Orientation
      getLeft  : ⦃ _ : orientation ≡ left ⦄ → L
      getRight : ⦃ _ : orientation ≡ right ⦄ → R

  record _⊎'_ {ℓˡ ℓʳ} (L : Set ℓˡ) (R : Set ℓʳ) {A : Set} ⦃ boolean : Boolean A ⦄ : Set (ℓˡ ⊔ ℓʳ) where
    field
      orientation : A
      getLeft  : ⦃ _ : orientation ≡ negative-value ⦄ → L
      getRight : ⦃ _ : orientation ≡ positive-value ⦄ → R

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

  _∈?_ : ∀ {ℓ} {A : Set ℓ} ⦃ eq? : Equality A ⦄ (a : A) (xs : List A) → Decidable (a ∈ xs)
  a ∈? [] = no λ ()
  _∈?_ ⦃ eq? ⦄ a (x ∷ xs) with a ≟ x
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
  get {kvs = []} associationList ()
  get {kvs = .(_ , v) ∷ kvs} (associationList ∷ k∉kvs ↦ v) (here .(car <$> kvs)) = v
  get {kvs = .(_ , v) ∷ kvs} (associationList ∷ k∉kvs ↦ v) (there x₁ _) = get associationList x₁

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
    var : (x : A) (isVariable : A → Bool) (formula : Formula A) ⦃ _ : isVariable x ≡ true ⦄ → ((purer x , isVariable) ⋐ formula)
    const : (x : A) (isVariable : A → Bool) ⦃ _ : isVariable x ≡ false ⦄ → ((purer x , isVariable) ⋐ purer x)
    freer[] : (isVariable : A → Bool) (𝑎 : Set ℓ) (f : 𝑎 → Freer List A) (𝑏 : Set ℓ) (g : 𝑏 → Freer List A) → (freer f [] , isVariable) ⋐ freer g []
    freer∷ : {isVariable : A → Bool} {𝑎 : Set ℓ} {f : 𝑎 → Freer List A} {𝑏 : Set ℓ} {g : 𝑏 → Freer List A}
             {x : 𝑎} {y : 𝑏} {xs : List 𝑎} {ys : List 𝑏} →
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
    var : (isVariable : A → Bool) (formula : Formula A) → ⦃ _ : isVariable x ≡ true ⦄ → x ∈ var x isVariable formula
    const : (isVariable : A → Bool) → ⦃ _ : isVariable x ≡ false ⦄ → x ∈ const x isVariable
    freer-head :
      {isVariable : A → Bool} {𝑎 : Set ℓ} {f : 𝑎 → Freer List A} {𝑏 : Set ℓ} {g : 𝑏 → Freer List A}
             {x' : 𝑎} {y : 𝑏} {xs : List 𝑎} {ys : List 𝑏} →
             {head : (f x' , isVariable) ⋐ g y} →
             (tail : (freer f xs , isVariable) ⋐ freer g ys) →
             x ∈ head →
             x ∈ freer∷ head tail
    freer-tail :
      {isVariable : A → Bool} {𝑎 : Set ℓ} {f : 𝑎 → Freer List A} {𝑏 : Set ℓ} {g : 𝑏 → Freer List A}
             {x' : 𝑎} {y : 𝑏} {xs : List 𝑎} {ys : List 𝑏} →
             (head : (f x' , isVariable) ⋐ g y) →
             {tail : (freer f xs , isVariable) ⋐ freer g ys} →
             x ∈ tail →
             x ∈ freer∷ head tail

  get : ∀ {ℓ} {A : Set ℓ} → {x : A} → {schema : Schema A} {formula : Formula A} → {schema⋐formula : schema ⋐ formula} → x ∈ schema⋐formula → Formula A
  get (var _ formula) = formula
  get {x = x} (const _) = purer x
  get (freer-head _ x∈head) = get x∈head
  get (freer-tail _ x∈tail) = get x∈tail

module Match where

  open Level
  open Freer
  open Formula
  open ListFunctor
  open module F = FormulaMembership
  open Schema
  open Product
  open Bool
  open Equality
  open List
  open module L = ListMembership
  open Overlay
  open module O = OverlayMembership
  open AssociationList

  Match : ∀ {ℓ} {A : Set ℓ} (schema : Schema A) (formula : Formula A) → Set (lsuc ℓ)
  Match {A = A} schema formula =
    Σ (schema ⋐ formula) λ overlay →
     (Σ (List (Σ A (λ _ → Formula A))) λ kvs →
      (Σ (AssociationList A (λ _ → Formula A) kvs) λ associationList →
         (∀ (v : A) →
            Schema.schema-isVariable schema v ≡ true →
            (v∈associationList : v L.∈ (car <$> kvs)) →
            (v∈formula : v F.∈ schema-formula schema) →
            (v∈overlay : v O.∈ overlay) →
            AssociationList.get associationList v∈associationList ≡ O.get v∈overlay
         ))
      )

module Records where

  open Level
  open Decidable
  open Empty

  record _IsMemberOf_
    { ℓᵉ } ( E : Set ℓᵉ )
    { ℓᵃ } ( A : Set ℓᵃ )
    : Set ( lsuc ( ℓᵉ ⊔ ℓᵃ ) )
    where
    constructor [_]
    field
      _∈_ : E → A → Set ( ℓᵉ ⊔ ℓᵃ )

    _∉_ : E → A → Set ( ℓᵉ ⊔ ℓᵃ )
    e ∉ a = ¬ (e ∈ a)

  open _IsMemberOf_ ⦃ ... ⦄

  module _ where
    open List
    private
      module L = ListMembership

    instance
      ListMembership : ∀ {ℓ} {A : Set ℓ} → A IsMemberOf (List A)
      ListMembership = [ L._∈_ ]

  module _ where
    open Formula
    open Schema
    private
      module O = Overlay
      module F = FormulaMembership

    instance
      OverlayMembership : ∀ {ℓ} {A : Set ℓ} → (Schema A) IsMemberOf (Formula A)
      OverlayMembership = [ O._⋐_ ]

      SchemaMembership : ∀ {ℓ} {A : Set ℓ} → A IsMemberOf (Schema A)
      SchemaMembership = [ (λ a schema → a F.∈ schema-formula schema) ]

      OverlayMembership₂ : ∀ {ℓ} {A : Set ℓ} {S : Schema A} {F : Formula A} → A IsMemberOf (_∈_ {{OverlayMembership}} S F)
      OverlayMembership₂ = [ (λ a → a OverlayMembership.∈_) ]

  module _ where
    open Equality

    record _HasValue_
      { ℓᵃ } ( A : Set ℓᵃ )
      { ℓᵇ } ( B : Set ℓᵇ )
      : Set (lsuc ( ℓᵃ ⊔ ℓᵇ ))
      where
      field
        value : A → B
        value' : (B' : Set ℓᵇ) → B ≡ B' → A → B

      hasSameValue : (a₁ a₂ : A) → Set ℓᵇ
      hasSameValue a₁ a₂ = value a₁ ≡ value a₂

  open _HasValue_ ⦃ ... ⦄

  module _ where
    open Formula
    open Schema
    private
      module O = OverlayMembership

    instance
      OverlayValue : ∀ {ℓ} {A : Set ℓ} {S : Schema A} {F : Formula A} {S∈F : _∈_ {{OverlayMembership}} S F} {a : A} → (_∈_ {{OverlayMembership₂}} a S∈F) HasValue (Formula A)
      OverlayValue = record { value = O.get ; value' = λ { .(Freer.Freer List.List _) Equality.refl → O.get } }

  record _IsDecidablyMemberOf_
    { ℓᵉ } ( E : Set ℓᵉ )
    { ℓᵃ } ( A : Set ℓᵃ )
    : Set ( lsuc ( ℓᵉ ⊔ ℓᵃ ) )
    where
    constructor [_]
    field
      overlap ⦃ membership ⦄ : E IsMemberOf A
      _∈?_ : (e : E) → (a : A) → Decidable ( e ∈ a )

  open _IsDecidablyMemberOf_ ⦃ ... ⦄

  module _ where
    open List
    open Equality

    private
      module L = ListMembership

    instance
      ListDecidableMembership : ∀ {ℓ} {A : Set ℓ} → ⦃ _ : Equality A ⦄ → A IsDecidablyMemberOf (List A)
      ListDecidableMembership = [ L._∈?_ ]

  module NewNewMatch' where

    open Level
    open Bool
    open Equality
    open List

    data Formula' {ℓ} (A : Set ℓ) : Set ℓ where
      atom : A → Formula' A
      compound : A → List (Formula' A) → Formula' A

  module NewNewMatch where

    open Level
    open Formula
    open Schema
    open Bool
    open Equality

    record RMatch
           {ℓ} {A : Set ℓ}
           {ℓ'} {Binding : Set ℓ'}
           ⦃ _ : A IsMemberOf Binding ⦄
           ⦃ _ : ∀ {a : A} {b : Binding} → (a ∈ b) HasValue (Formula A) ⦄
           (schema : Schema A) (formula : Formula A)
           : Set (ℓ' ⊔ lsuc ℓ) where
      field
        overlay : schema ∈ formula
        binding : Binding
        law1 : ∀ (v : A) →
                 (v∈b : v ∈ binding) →
                 (v∈overlay : v ∈ overlay) →
                 _≡_ {A = Formula A} (value v∈b) (value v∈overlay)
        law2 : (v : A) →
               Schema.schema-isVariable schema v ≡ true →
               v ∈ binding →
               v ∈ overlay
        law3 : (v : A) →
               Schema.schema-isVariable schema v ≡ true →
               v ∈ overlay →
               v ∈ binding
        law4 : (c : A) →
               Schema.schema-isVariable schema c ≡ false →
               c ∉ binding

    record RFormula {ℓ} {A : Set ℓ} : Set (lsuc ℓ) where


  module NewMatch where

    open Level
    open Freer
    open Formula
    open ListFunctor
    private module F = FormulaMembership
    open Schema
    open Product
    open Bool
    open Equality
    open List
    private module L = ListMembership
    open Overlay
    private module O = OverlayMembership
    open AssociationList
    open Empty
    open import Prelude.Function

    record RMatch
           {ℓ} {A : Set ℓ}
           {ℓ'} {Binding : Set ℓ'}
           ⦃ _ : A IsMemberOf Binding ⦄
           ⦃ _ : ∀ {a : A} {b : Binding} → (a ∈ b) HasValue (Formula A) ⦄ (schema : Schema A) (formula : Formula A) : Set (ℓ' ⊔ lsuc ℓ) where
      field
        overlay : schema ∈ formula
        binding : Binding
        law1 : ∀ (v : A) →
                 (v∈b : v ∈ binding) →
                 (v∈overlay : v ∈ overlay) →
                 _≡_ {A = Formula A} (value v∈b) (value v∈overlay)
        law2 : (v : A) →
               Schema.schema-isVariable schema v ≡ true →
               v ∈ binding →
               v ∈ overlay
        law3 : (v : A) →
               Schema.schema-isVariable schema v ≡ true →
               v ∈ overlay →
               v ∈ binding
        law4 : (c : A) →
               Schema.schema-isVariable schema c ≡ false →
               c ∉ binding

    Match : ∀ {ℓ} {A : Set ℓ}
            {ℓ'} {Binding : Set ℓ'}
            ⦃ A∈B : A IsMemberOf Binding ⦄
            ⦃ A∈BHasValueF : ∀ {a : A} {b : Binding} → (a ∈ b) HasValue (Formula A) ⦄
            (schema : Schema A) (formula : Formula A)
            → Set (ℓ' ⊔ lsuc ℓ)
    Match {A = A} {Binding = Binding} schema formula =
        Σ (schema ∈ formula) λ overlay →
          Σ Binding λ binding →
             (∀ (v : A) →
                Schema.schema-isVariable schema v ≡ true →
                (v∈b : v ∈ binding) →
                (v∈overlay : v ∈ overlay) →
                _≡_ {A = Formula A} (value v∈b) (value v∈overlay)
             )

-- -- -- -- --   -- --   data ⟦_/_⋐_⟧ : (X : Free List A) (isVariable : A → Bool) (Y : Free List B) → Set (sucₗ α) where
-- -- -- -- --   -- --     PurePure : (x y : A) → pure x ⋐ pure y
-- -- -- -- --   -- --     PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
-- -- -- -- --   -- --     FreeFree : {M N : Set α} →
-- -- -- -- --   -- --                {f : M → Free List A} →
-- -- -- -- --   -- --                {m : M} {ms : List M} →
-- -- -- -- --   -- --                {g : N → Free List A} →
-- -- -- -- --   -- --                {n : N} {ns : List N} →
-- -- -- -- --   -- --                ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
-- -- -- -- --   -- --                f m ⋐ g n →
-- -- -- -- --   -- --                free f ms ⋐ free g ns →
-- -- -- -- --   -- --                free f (m ∷ ms) ⋐ free g (n ∷ ns)

-- -- -- -- -- -- mutual
-- -- -- -- -- --   infixl 1 _∷_↦_
-- -- -- -- -- --   data Map {ℓk} (K : Set ℓk) {ℓv} (V : K → Set ℓv) : List (Σ K V) → Set (ℓk ⊔ ℓv) where
-- -- -- -- -- --     [] : Map K V []
-- -- -- -- -- --     _∷_↦_
-- -- -- -- -- --       : {l : List (Σ K V)} (map : Map K V l)
-- -- -- -- -- --         {k : K} (k∉map : k ∉ map) → (v : V k) → Map K V (k , v ∷ l)

-- -- -- -- -- --   data _∈_ {a} {K : Set a} (k : K) {b} {V : K → Set b} : Map K V → Set (a ⊔ b) where
-- -- -- -- -- --     here : ∀ (map : Map K V) → (k∉map : k ∉ map) → (v : V k) → k ∈ (map ∷ k∉map ↦ v)

-- -- -- -- -- --   _∉_ : ∀ {a} {K : Set a} → K → ∀ {b} {V : K → Set b} (map : Map K V) → Set (a ⊔ b)
-- -- -- -- -- --   k ∉ map = ¬ k ∈ map

-- -- -- -- -- -- {-
-- -- -- -- -- -- mutual
-- -- -- -- -- --   infixl 1 _∷_↦_
-- -- -- -- -- --   data Map {ℓk} (K : Set ℓk) {ℓv} (V : K → Set ℓv) : Set (ℓk ⊔ ℓv) where
-- -- -- -- -- --     [] : Map K V
-- -- -- -- -- --     _∷_↦_ : (map : Map K V) {k : K} (k∉map : k ∉ map) → V k → Map K V

-- -- -- -- -- --   data _∈_ {a} {K : Set a} (k : K) {b} {V : K → Set b} : Map K V → Set (a ⊔ b) where
-- -- -- -- -- --     here : ∀ (map : Map K V) → (k∉map : k ∉ map) → (v : V k) → k ∈ (map ∷ k∉map ↦ v)

-- -- -- -- -- --   _∉_ : ∀ {a} {K : Set a} → K → ∀ {b} {V : K → Set b} (map : Map K V) → Set (a ⊔ b)
-- -- -- -- -- --   k ∉ map = ¬ k ∈ map
-- -- -- -- -- -- -}
