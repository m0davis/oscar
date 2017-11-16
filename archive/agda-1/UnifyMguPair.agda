
module UnifyMguPair where

open import UnifyTerm
open import UnifyMgu
open import UnifyMguCorrect

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Function using (_∘_; id; case_of_; _$_)
open import Relation.Nullary
open import Data.Product
open import Data.Empty
open import Data.Maybe
open import Data.Sum

l1 : ∀ m → Data.Fin.toℕ (Data.Fin.fromℕ m) ≡ m
l1 zero = refl
l1 (suc m) = cong suc (l1 m)

l2 : ∀ m → m ≡ m + 0
l2 zero = refl
l2 (suc m) = cong suc (l2 m)

fixup : ∀ m → Fin (Data.Fin.toℕ (Data.Fin.fromℕ m) + m) → Fin (m + (m + 0))
fixup m x rewrite l1 m | sym (l2 m) = x

revise-down : ∀ {m} → Fin m → Fin (2 * m)
revise-down {m} x = Data.Fin.inject+ (m + 0) x

revise-up : ∀ {m} → Fin m → Fin (2 * m)
revise-up {m} x = fixup m (Data.Fin.fromℕ m Data.Fin.+ x)

write-variable-down : ∀ {m} → Term m → Term (2 * m)
write-variable-down {m} (i l) = i $ revise-down l
write-variable-down {m} leaf = leaf
write-variable-down {m} (s fork t) = write-variable-down s fork write-variable-down t

write-variable-up : ∀ {m} → Term m → Term (2 * m)
write-variable-up {m} (i r) = i (revise-up r)
write-variable-up {m} leaf = leaf
write-variable-up {m} (s fork t) = write-variable-up s fork write-variable-up t

write-variables-apart : ∀ {m} (s t : Term m) → Term (2 * m) × Term (2 * m)
write-variables-apart s t = write-variable-down s , write-variable-up t

separate-substitutions-down : ∀ {m n} → (Fin (2 * m) → Term n) → Fin m → Term n
separate-substitutions-down {m} f x = f $ revise-down x

separate-substitutions-up : ∀ {m n} → (Fin (2 * m) → Term n) → Fin m → Term n
separate-substitutions-up {m} f x = f $ revise-up x

separate-substitutions : ∀ {m n} → (Fin (2 * m) → Term n) → (Fin m → Term n) × (Fin m → Term n)
separate-substitutions {m} x = separate-substitutions-down {m} x , separate-substitutions-up {m} x

write≡separate : ∀ {m n} (σ : AList (2 * m) n) (t : Term m) → (sub σ ◃_) (write-variable-down t) ≡ ((separate-substitutions-down $ sub σ) ◃_) t
write≡separate {zero} {.0} anil (i x) = refl
write≡separate {suc m} {.(suc (m + suc (m + 0)))} anil (i x) = refl
write≡separate {suc m} {n} (σ asnoc t' / x) (i x₁) = refl
write≡separate σ leaf = refl
write≡separate σ (t₁ fork t₂) = cong₂ _fork_ (write≡separate σ t₁) (write≡separate σ t₂)

write≡separate' : ∀ {m n} (σ : AList (2 * m) n) (t : Term m) → (sub σ ◃_) (write-variable-down t) ≡ ((separate-substitutions-down $ sub σ) ◃_) t
write≡separate' {zero} {.0} anil (i x) = refl
write≡separate' {suc m} {.(suc (m + suc (m + 0)))} anil (i x) = refl
write≡separate' {suc m} {n} (σ asnoc t' / x) (i x₁) = refl
write≡separate' σ leaf = refl
write≡separate' σ (t₁ fork t₂) = cong₂ _fork_ (write≡separate σ t₁) (write≡separate σ t₂)

Property'2 : (m : ℕ) -> Set1
Property'2 m = ∀ {n} -> (Fin (2 * m) -> Term n) -> Set

Nothing'2 : ∀{m} -> (P : Property'2 m) -> Set
Nothing'2 P = ∀{n} f -> P {n} f -> ⊥

Unifies'2 : ∀ {m} (s t : Term m) -> Property'2 m
Unifies'2 s t f =
  let --s' , t' = write-variables-apart s t
      f₁ , f₂ = separate-substitutions f
  in f₁ ◃ s ≡ f₂ ◃ t

pair-mgu' : ∀ {m} -> (s t : Term m) -> Maybe (∃ (AList (2 * m)))
pair-mgu' {m} s t =
  let s' , t' = write-variables-apart s t
      mgu' = mgu s' t'
  in
    mgu'

up-equality : ∀ {m n} {f : (2 * m) ~> n} (t : Term m) → (f ∘ revise-up) ◃ t ≡ f ◃ write-variable-up t
up-equality (i x) = refl
up-equality leaf = refl
up-equality (t₁ fork t₂) = cong₂ _fork_ (up-equality t₁) (up-equality t₂)

down-equality : ∀ {m n} {f : (2 * m) ~> n} (t : Term m) → (f ∘ revise-down) ◃ t ≡ f ◃ write-variable-down t
down-equality (i x) = refl
down-equality leaf = refl
down-equality (t₁ fork t₂) = cong₂ _fork_ (down-equality t₁) (down-equality t₂)

revise-to-write : ∀ {m n} {f : (2 * m) ~> n} (s t : Term m) → (f ∘ revise-down) ◃ s ≡ (f ∘ revise-up) ◃ t → f ◃ write-variable-down s ≡ f ◃ write-variable-up t
revise-to-write (i x) (i x₁) x₂ = x₂
revise-to-write (i x) leaf x₁ = x₁
revise-to-write (i x) (t fork t₁) x₁ = trans x₁ (up-equality (t fork t₁))
revise-to-write leaf (i x) x₁ = x₁
revise-to-write leaf leaf x = refl
revise-to-write leaf (t₁ fork t₂) x = trans x (up-equality (t₁ fork t₂))
revise-to-write (s₁ fork s₂) (i x) x₁ = trans (sym (down-equality (s₁ fork s₂))) x₁
revise-to-write (s₁ fork s₂) leaf x = trans (sym (down-equality (s₁ fork s₂))) x
revise-to-write (s₁ fork s₂) (t₁ fork t₂) x = trans (trans (sym (down-equality (s₁ fork s₂))) x) (up-equality (t₁ fork t₂))

write-to-revise : ∀ {m n} {f : (2 * m) ~> n} (s t : Term m) → f ◃ write-variable-down s ≡ f ◃ write-variable-up t → (f ∘ revise-down) ◃ s ≡ (f ∘ revise-up) ◃ t
write-to-revise (i x) (i x₁) x₂ = x₂
write-to-revise (i x) leaf x₁ = x₁
write-to-revise (i x) (t fork t₁) x₁ = trans x₁ (sym (up-equality (t fork t₁)))
write-to-revise leaf (i x) x₁ = x₁
write-to-revise leaf leaf x = refl
write-to-revise leaf (t fork t₁) x = trans x (sym (up-equality (t fork t₁)))
write-to-revise (s₁ fork s₂) (i x) x₁ = trans ((down-equality (s₁ fork s₂))) x₁
write-to-revise (s₁ fork s₂) leaf x = trans ((down-equality (s₁ fork s₂))) x
write-to-revise (s₁ fork s₂) (t fork t₁) x = trans (trans ((down-equality (s₁ fork s₂))) x) (sym (up-equality (t fork t₁)))

pair-mgu-c' : ∀ {m} (s t : Term m) ->
                (∃ λ n → ∃ λ σ → (Max⋆ (Unifies'2 s t)) (sub σ) × pair-mgu' s t ≡ just (n , σ))
                ⊎ (Nothing⋆ (Unifies'2 s t)                     × pair-mgu' s t ≡ nothing)
pair-mgu-c' {m} s t with write-variable-down s | write-variable-up t | inspect write-variable-down s | inspect write-variable-up t
… | s' | t' | [[ refl ]] | [[ refl ]] with mgu-c s' t'
… | (inj₁ (n , σ , (σ◃s'=σ◃t' , max-σ) , amgu=just)) =
  inj₁ $
  n ,
  σ ,
  ( write-to-revise s t σ◃s'=σ◃t' ,
    ( λ {n'} f f◃s≡f◃t → (proj₁ $ max-σ f (revise-to-write s t f◃s≡f◃t)) ,
      (λ x → proj₂ (max-σ f (revise-to-write s t f◃s≡f◃t)) x) ) ) ,
  amgu=just
… | (inj₂ (notunified , amgu=nothing)) = inj₂ ((λ {n} f x → notunified f (revise-to-write s t x)) , amgu=nothing)
