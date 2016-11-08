
module IMatch where

open import Agda.Primitive

record ⟦Membership_∈_⟧
  { ℓᵉ } ( E : Set ℓᵉ )
  { ℓᵃ } ( A : Set ℓᵃ )
  : Set ( lsuc ( ℓᵉ ⊔ ℓᵃ ) )
  where
  constructor [_]
  field
    [_∈_] : E → A → Set ( ℓᵉ ⊔ ℓᵃ )

open ⟦Membership_∈_⟧ ⦃ ... ⦄

record ⟦Subset_∈_⊆_⟧
  { ℓᵉ } ( E : Set ℓᵉ )
  { ℓᵃ } ( A : Set ℓᵃ )
  { ℓᵇ } ( B : Set ℓᵇ )
  ⦃ ⟦E∈A⟧ : ⟦Membership E ∈ A ⟧ ⦄
  ⦃ ⟦E∈B⟧ : ⟦Membership E ∈ B ⟧ ⦄
  : Set ( lsuc ( ℓᵉ ⊔ ℓᵃ ⊔ ℓᵇ ) )
  where
  constructor [_,_,_]
  field
    [_⊆_]
      : A → B → Set ( ℓᵃ ⊔ ℓᵇ )
    sound
      : { a : A } { b : B }
      → [ a ⊆ b ]
      → { e : E } → [ e ∈ a ] → [ e ∈ b ]
    complete
      : { a : A } { b : B }
      → ( { e : E } → [ e ∈ a ] → [ e ∈ b ] )
      → [ a ⊆ b ]

open ⟦Subset_∈_⊆_⟧ ⦃ ... ⦄

open import Agda.Builtin.List renaming ([] to ∅)
open import Agda.Builtin.Nat

id : ∀ { ℓᵃ } { A : Set ℓᵃ } → A → A
id x = x

instance
  ⟦⋆∈List⋆⟧
    : ∀ { ℓᵃ } { A : Set ℓᵃ } → ⟦Membership A ∈ List A ⟧
  ⟦⋆∈List⋆⟧ { ℓᵃ } { A } = record { [_∈_] = _∈_ }
    module ⟦⋆∈List⋆⟧ where
    data _∈_ : A → List A → Set ℓᵃ where
      _∷_
        : ( x : A ) ( as : List A ) → x ∈ ( x ∷ as )
      _∷∈_
        : ( a : A ) { x : A } { as : List A } → x ∈ as → x ∈ ( a ∷ as )

  open ⟦⋆∈List⋆⟧

  ⟦⋆∈List⋆⊆List⋆⟧
    : ∀ { ℓᵃ } { A : Set ℓᵃ } → ⟦Subset A ∈ List A ⊆ List A ⟧
  ⟦⋆∈List⋆⊆List⋆⟧ = record { [_⊆_] = _⊆_ ; sound = id ; complete = id }
    module ⟦⋆∈List⋆⊆List⋆⟧ where
      _⊆_ : List _ → List _ → Set _
      as ⊆ bs = ∀ {x : _} → x ∈ as → x ∈ bs

  open ⟦⋆∈List⋆⊆List⋆⟧

record ⟦Pure_⟧ { ℓᵃ } ( A : Set ℓᵃ ) : Set ℓᵃ where
  constructor [_]
  field
    [] : A

open ⟦Pure_⟧ ⦃ ... ⦄

data FreerConstructor : Set where
  pure : FreerConstructor
  free : FreerConstructor

open import Agda.Builtin.Equality

mutual
  record ⟦Freer_over_⟧
    { ℓᵃ } { ℓᵇ }
    ( F : Set ℓᵃ → Set ℓᵇ )
    ( A : Set ℓᵃ )
    : Set ( lsuc ( ℓᵃ ⊔ ℓᵇ ) )
    where
    inductive
    field
      destructor : FreerConstructor
      [pure] : ⦃ _ : destructor ≡ pure ⦄ → ⟦Pure A ⟧
      [free] : ⦃ _ : destructor ≡ free ⦄ → ⟦FreeFreer F over A ⟧

  record ⟦FreeFreer_over_⟧
    { ℓᵃ } { ℓᵇ }
    ( F : Set ℓᵃ → Set ℓᵇ )
    ( A : Set ℓᵃ )
    : Set ( lsuc ( ℓᵃ ⊔ ℓᵇ ) )
    where
    inductive
    field
      {[domain]} : Set ℓᵃ
      [f] : [domain] → ⟦Freer F over A ⟧
      [F] : F [domain]

record ⟦Formula_⟧ { a } ( A : Set a ) : Set ( lsuc a ) where
  field
    formula : ⟦Freer List over A ⟧

open ⟦Formula_⟧

record ⟦Schema_⟧ {a} (A : Set a) : Set (lsuc a) where
  field
    formula : ⟦Formula A ⟧
    isVariable : A → Set a

  variables : List A
  variables = {!!}

open ⟦Schema_⟧

record IOverlay {s} {S : Set s} (Schema : ⟦Schema S ⟧)
                {f} {F : Set f} (Formula : ⟦Formula F ⟧)
                : Set (lsuc (s ⊔ f)) where
  field
    carrier : Set (s ⊔ f)

open IOverlay

record IBinding {ℓₖ} {K : Set ℓₖ}
                {ℓᵥ} (V : K → Set ℓᵥ)
                : Set (lsuc (ℓₖ ⊔ ℓᵥ)) where
  field
    carrier : Set (ℓₖ ⊔ ℓᵥ)
    keys : Set ℓₖ
    value : (k : K) → V k

open IBinding

open import Agda.Builtin.Equality

record IMatch {s} {S : Set s} (Schema : ⟦Schema S ⟧)
              {f} {F : Set f} (Formula : ⟦Formula F ⟧)
              ⦃ Overlay : ⟦Schema S ⟧ → ⟦Formula F ⟧ → IOverlay Schema Formula ⦄
              ⦃ Binding : IBinding (λ (_ : S) → F) ⦄
              ⦃ ElementBinding : ⟦Membership S ∈ keys Binding ⟧ ⦄
              --⦃ ElementSchema : ⟦Membership S ∈ formula Schema ⟧ ⦄
              : Set (lsuc (s ⊔ f)) where
  field
    --schema : formula Schema
    --formula : carrier Formula
    overlay : carrier (Overlay Schema Formula)
    binding : carrier Binding
    --schema-variables-are-a-subset-of-binding-keys : ⟦Subset S ∈ variables Schema ⊆ keys Binding ⟧
    --overlay-variables-have-same-value-as-binding : (o : k ∈ overlay) → (b : k ∈ binding) → value o ≡ value b

--    overlay : schema overlays formula
