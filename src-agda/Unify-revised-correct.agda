
module Unify-revised-correct where

--open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Prelude.Function

postulate
  Nat : Set
  Term : Nat → Set
  _~>_ : Nat → Nat → Set -- Fin → Term
  _=>_ : Nat → Nat → Set -- Fin → Fin
  ε : ∀ {m n} → m ~> n
  ▹ : ∀ {m n} -> m => n -> m ~> n
  _◃_ : ∀ {m n} → m ~> n → Term m → Term n
  _≐_ : {m n : Nat} → (m ~> n) → (m ~> n) → Set
  ◃ext : ∀ {m n} {f g : m ~> n} → f ≐ g → ∀ t → f ◃ t ≡ g ◃ t
  _◇_ : ∀ {l m n : Nat} → m ~> n → l ~> m → l ~> n
  _◆_ : ∀ {l m n : Nat} → m ~> n → l => m → l ~> n
  ≐-cong : ∀ {m n o} {f : m ~> n} {g} (h : _ ~> o) → f ≐ g → (h ◇ f) ≐ (h ◇ g)
  ≐-sym : ∀ {m n} {f : m ~> n} {g} → f ≐ g → g ≐ f
  subFact1 : ∀ {n} → (t : Term n) → ε ◃ t ≡ t
  subFact2 : ∀ {l m n} → (f : m ~> n) (g : _) (t : Term l) → (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)
  subFact3 : ∀ {l m n} (f : m ~> n) (r : l => m) -> f ◇ ▹ r ≡ f ◆ r

open import Prelude.Equality

◃ext' : ∀ {m n o} {f : m ~> n}{g : m ~> o}{h} -> f ≐ (h ◇ g) -> ∀ t -> f ◃ t ≡ h ◃ (g ◃ t)
◃ext' p t = trans (◃ext p t) (subFact2 _ _ t)
