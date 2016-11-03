{-# OPTIONS --exact-split #-}
module Free where

open import Level
--open import Function
--open import Category.Functor

data Free {𝑨 𝑩} (F : Set 𝑨 → Set 𝑩) (A : Set 𝑨) : Set (suc (𝑨 ⊔ 𝑩)) where
  pure : A → Free F A
  free : ∀ {𝑎 : Set 𝑨} → (𝑎 → Free F A) → F 𝑎 → Free F A

mapFree : ∀ {𝑨 𝑩} {F : Set 𝑨 → Set 𝑩} {A B : Set 𝑨} → (fun : A → B) → Free F A → Free F B
mapFree fun (pure x) = pure (fun x)
mapFree fun (free x x₁) = free (λ x₂ → mapFree fun (x x₂)) x₁
{-
record RawFunctor {ℓ ℓ'} (F : Set ℓ → Set ℓ') : Set (suc (ℓ ⊔ ℓ')) where
  infixl 4 _<$>_ _<$_

  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ y = const x <$> y

instance
  FreeFunctor : ∀ {𝑨 𝑩} {F : Set 𝑨 → Set 𝑩} → RawFunctor (Free F)
  FreeFunctor = record { _<$>_ = mapFree }
-}
open import Prelude.List
open import Prelude.Bool

module _ {a} (A : Set a) where
  Expression = Free List A
  record Formula : Set (suc a) where
    constructor _,_
    field
      expression : Expression
      isVariable : A → Bool

open import Prelude.Empty
open import Prelude.Function
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Equality.Inspect
open import Tactic.Reright

{-
module M {a} {A : Set a} {B : Set a} (IsVariable : B → Set) (DecIsVariable : (b : B) → Dec (IsVariable b)) {C : Set a} (DecC : (c1 c2 : C) → Dec (c1 ≡ c2)) (A→C : A → C) (B→C : B → C) where
  data _⋐_ : (exp : Free List A) (pat : Free List B) → Set (suc a) where
    var : (exp : Free List A) → {y : B} → ( _ : IsVariable y ) → exp ⋐ pure y
    pure : (x : A) (y : B) → ¬ IsVariable y  → A→C x ≡ B→C y → pure x ⋐ pure y
    free[] : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set a} (g : 𝑏 → Free List B) → free f [] ⋐ free g []
    free∷ : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set a} (g : 𝑏 → Free List B) (x : 𝑎) (xs : List 𝑎) (y : 𝑏) (ys : List 𝑏) → f x ⋐ g y → free f xs ⋐ free g ys → free f (x ∷ xs) ⋐ free g (y ∷ ys)

  _⋐?_ : (exp : Free List A) (pat : Free List B) → Dec (exp ⋐ pat)
  exp ⋐? pure y with DecIsVariable y
  exp ⋐? pure y | yes x = yes (var exp x)
  pure x₁ ⋐? pure y | no x with DecC (B→C y) (A→C x₁)
  ... | yes cc = yes (pure x₁ y x (sym cc))
  ... | no ncc = no (λ { (var .(pure _) x₂) → x x₂ ; (pure _ _ x₂ x₃) → ncc (sym x₃)})
  free x₁ x₂ ⋐? pure y | no x = {!!}
  pure x ⋐? free g ys  = {!!}
  free x x₁ ⋐? free x₂ x₃ = {!!}
-}
record _≡'_ {a} {A : Set a} (x : A) (x' : A) : Set a where
  inductive
  field
    refl' : x ≡' x'

module M1 {a} {A : Set a} {B : Set a} (IsVariable : B → Bool) {C : Set a} (DecC : (c1 c2 : C) → Dec (c1 ≡ c2)) (A→C : A → C) (B→C : B → C) where
  data _⋐_ : (exp : Free List A) (pat : Free List B) → Set (suc a) where
    var : (exp : Free List A) → {y : B} → IsTrue (IsVariable y) → exp ⋐ pure y
    pure : (x : A) (y : B) → IsFalse (IsVariable y) → A→C x ≡ B→C y → pure x ⋐ pure y
    free[] : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set a} (g : 𝑏 → Free List B) → free f [] ⋐ free g []
    free∷ : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set a} (g : 𝑏 → Free List B) (x : 𝑎) (xs : List 𝑎) (y : 𝑏) (ys : List 𝑏) → f x ⋐ g y → free f xs ⋐ free g ys → free f (x ∷ xs) ⋐ free g (y ∷ ys)

  foo : ∀ y → IsTrue (IsVariable y) → IsVariable y ≡ false → ⊥
  foo y x x₁ = case transport IsTrue x₁ x of λ ()

  _⋐?_ : (exp : Free List A) (pat : Free List B) → Dec (exp ⋐ pat)
  exp ⋐? pure y with IsVariable y | graphAt IsVariable y
  exp ⋐? pure y | true | ingraph x = yes (var exp (transport IsTrue (sym x) true))
  pure x ⋐? pure y | false | ingraph eq with DecC (A→C x) (B→C y)
  ... | yes eq2 = yes (pure x y (transport IsFalse (sym eq) false) eq2)
  ... | no neq2 = no (λ { (var .(pure x) x₁) → case transport IsTrue eq x₁ of λ () ; (pure .x _ x₁ x₂) → neq2 x₂})
  free x x₁ ⋐? pure y | false | ingraph eq = no (λ { (var .(free x x₁) x₂) → case transport IsTrue eq x₂ of λ ()})
  pure x ⋐? free g ys  = no (λ ())
  free f [] ⋐? free g [] = yes (free[] _ _)
  free f [] ⋐? free g (x ∷ ys) = {!!}
  free f (x ∷ xs) ⋐? free g [] = {!!}
  free f (x ∷ xs) ⋐? free g (x₁ ∷ ys) = {!!}

{-
module M {a} {A : Set a} {B : Set a} (IsVariable : B → Bool) {C : Set a} (DecC : (c1 c2 : C) → Dec (c1 ≡ c2)) (A→C : A → C) (B→C : B → C) where
  data _⋐_ : (exp : Free List A) (pat : Free List B) → Set (suc a) where
    var : (exp : Free List A) → {y : B} → IsVariable y ≡ true → exp ⋐ pure y
    pure : (x : A) (y : B) → IsVariable y ≡ false → A→C x ≡ B→C y → pure x ⋐ pure y
    free[] : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set a} (g : 𝑏 → Free List B) → free f [] ⋐ free g []
    free∷ : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set a} (g : 𝑏 → Free List B) (x : 𝑎) (xs : List 𝑎) (y : 𝑏) (ys : List 𝑏) → f x ⋐ g y → free f xs ⋐ free g ys → free f (x ∷ xs) ⋐ free g (y ∷ ys)

  _⋐?_ : (exp : Free List A) (pat : Free List B) → Dec (exp ⋐ pat)
  exp ⋐? pure y with IsVariable y | graphAt IsVariable y
  exp ⋐? pure y | true | ingraph x = yes (var exp {!!})
  pure x ⋐? pure y | false | ingraph eq with DecC (A→C x) (B→C y)
  ... | yes eq2 = yes (pure x y ({!!}) eq2)
  ... | no neq2 = no (λ { (var .(pure x) x₁) → case {!!} of λ () ; (pure .x _ x₁ x₂) → neq2 x₂})
  free x x₁ ⋐? pure y | false | ingraph eq = no (λ { (var .(free x x₁) x₂) → case {!!} of λ ()})
  pure x ⋐? free g ys  = no (λ ())
  free f [] ⋐? free g [] = yes (free[] _ _)
  free f [] ⋐? free g (x ∷ ys) = {!!}
  free f (x ∷ xs) ⋐? free g [] = {!!}
  free f (x ∷ xs) ⋐? free g (x₁ ∷ ys) = {!!}
-}
{-
module M {a} {A : Set a} {b} {B : Set b} (isVariable : B → Bool) (_∼_ : A → B → Bool) where
  data _⋐_ : (exp : Free List A) (pat : Free List B) → Set (suc (a ⊔ b)) where
    var : (exp : Free List A) → {y : B} → isVariable y ≡ true → exp ⋐ pure y
    pure : (x : A) (y : B) → isVariable y ≡ false → x ∼ y ≡ true → pure x ⋐ pure y
    free[] : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set b} (g : 𝑏 → Free List B) → free f [] ⋐ free g []
    free∷ : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set b} (g : 𝑏 → Free List B) (x : 𝑎) (xs : List 𝑎) (y : 𝑏) (ys : List 𝑏) → f x ⋐ g y → free f xs ⋐ free g ys → free f (x ∷ xs) ⋐ free g (y ∷ ys)

  _⋐?_ : (exp : Free List A) (pat : Free List B) → Dec (exp ⋐ pat)
  exp ⋐? pure y with isVariable y | graphAt isVariable y
  exp ⋐? pure y | true | ingraph isVariable'y≡true = yes (var exp isVariable'y≡true)
  pure x ⋐? pure y | false | ingraph isVariable'y≡false with x ∼ y | graphAt (x ∼_) y
  ... | true | ingraph x∼y≡true = yes (pure x y isVariable'y≡false x∼y≡true)
  ... | false | ingraph x∼y =
    no λ
    { (var _ y-is-var) → case transport (_≡ false) y-is-var isVariable'y≡false of {!!}
    ; (pure .x _ x₁ x₂) → {!!}}
  free x x₁ ⋐? pure y | false | ingraph eq = no (λ { (var .(free x x₁) x₂) → case {!!} of λ ()})
  pure x ⋐? free g ys  = no (λ ())
  free f [] ⋐? free g [] = yes (free[] _ _)
  free f [] ⋐? free g (x ∷ ys) = {!!}
  free f (x ∷ xs) ⋐? free g [] = {!!}
  free f (x ∷ xs) ⋐? free g (x₁ ∷ ys) = {!!}
-}

module M {a} {A : Set a} {b} {B : Set b} (isVariable : B → Bool) (_∼_ : A → B → Bool) where
  data _⋐_ : (exp : Free List A) (pat : Free List B) → Set (suc (a ⊔ b)) where
    var : (exp : Free List A) → {y : B} → isVariable y ≡ true → exp ⋐ pure y
    pure : (x : A) (y : B) → isVariable y ≡ false → x ∼ y ≡ true → pure x ⋐ pure y
    free[] : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set b} (g : 𝑏 → Free List B) → free f [] ⋐ free g []
    free∷ : {𝑎 : Set a} (f : 𝑎 → Free List A) {𝑏 : Set b} (g : 𝑏 → Free List B) (x : 𝑎) (xs : List 𝑎) (y : 𝑏) (ys : List 𝑏) → f x ⋐ g y → free f xs ⋐ free g ys → free f (x ∷ xs) ⋐ free g (y ∷ ys)

  _⋐?_ : (exp : Free List A) (pat : Free List B) → Dec (exp ⋐ pat)
  exp ⋐? pure y with isVariable y | graphAt isVariable y
  exp ⋐? pure y | true | ingraph isVariable'y≡true = yes (var exp {!!})
  pure x ⋐? pure y | false | ingraph isVariable'y≡false with x ∼ y | graphAt (x ∼_) y
  ... | true | ingraph x∼y≡true = yes (pure x y isVariable'y≡false x∼y≡true)
  ... | false | ingraph x∼y =
    no λ
    { (var _ y-is-var) → case transport (_≡ false) y-is-var isVariable'y≡false of {!!}
    ; (pure .x _ x₁ x₂) → {!!}}
  free x x₁ ⋐? pure y | false | ingraph eq = no (λ { (var .(free x x₁) x₂) → case {!!} of λ ()})
  pure x ⋐? free g ys  = no (λ ())
  free f [] ⋐? free g [] = yes (free[] _ _)
  free f [] ⋐? free g (x ∷ ys) = {!!}
  free f (x ∷ xs) ⋐? free g [] = {!!}
  free f (x ∷ xs) ⋐? free g (x₁ ∷ ys) = {!!}


    --p,pp : {x : A} → {y : B} → x  y → pure x ⋐ pure y





-- -- -- if P and (if P then Q) then Q
-- -- -- if A then B = if x ∈ A then x ∈ B = A is a subset of B
-- -- -- if A then B = A only if B = A necessitates B
-- -- -- A is true only in a subset of the universes in which B is true
-- -- -- i.e. if

-- -- -- so, if A is true, then B is true
-- -- -- so the {x | A is true in x} ⊂ {x | B is true in x}
-- -- -- ⇒
-- -- -- ⊂


-- -- --   -- PurePure : (x y : A) → pure x ⋐ pure y
-- -- --   -- PureFree : (x : A) → ∀ {N : Set α} → (g : N → Free List A) → (ns : List N) → pure x ⋐ free g ns
-- -- --   -- FreeFree : {M N : Set α} →
-- -- --   --            {f : M → Free List A} →
-- -- --   --            {m : M} {ms : List M} →
-- -- --   --            {g : N → Free List A} →
-- -- --   --            {n : N} {ns : List N} →
-- -- --   --            ¬ free f (m ∷ ms) ≞ free g (n ∷ ns) →
-- -- --   --            f m ⋐ g n →
-- -- --   --            free f ms ⋐ free g ns →
-- -- --   --            free f (m ∷ ms) ⋐ free g (n ∷ ns)
