
module Oscar.Definition where

{-

unpack : AList m n → Fin m → Term n -- sub
substitute : (Fin m → Term n) → Term m → Term n -- _◃_
substitutes : ∀ N → (Fin m → Term n) → Terms N m → Terms N n -- _◃s_
stepify : (Term m → Term n) → Step m → Step n -- fmapS
collapse : (List ∘ Step) n → Term n → Term n -- _⊹_

Substitist =
Substitunction = Fin m → Term n

Oscar.Data.Proposequality
Oscar.Data.Proposextensequality
Oscar.Data.Term
Oscar.Data.Terms
Oscar.Data.PropositionalEquality
  setoidPropositionalEquality : Set → Setoid
Oscar.Data.IndexedPropositionalEquality
  setoidIndexedPropEq : ∀ {A : Set} {B : A → Set} → ((x : A) → B x) → ((x : A) → B x) → Setoid
Oscar.Data.Substitist


Oscar.Setoid.PropositionalEquality
Oscar.Morphism.Substitist
Oscar.Unification
Oscar.Data.Substitunction
  Substitunction m n = Fin m → Term n
  : Morphism ℕ
  :


Oscar.Definition.Substitist
  : Morphism ℕ
  = alistSetoid
  : IsSemigroupoid
  : Semigroupoid _++_
  : IsCategory
  : Category
  Oscar.Definition.Substitist.internal
    AList
    alistSetoid : ℕ → ℕ → Setoid
    ε = anil
    _++_


-}
