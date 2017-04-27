
module Oscar.Data.Vec.Properties where

open import Oscar.Data.Vec
open import Data.Vec.Properties public

open import Data.Nat
open import Data.Product renaming (map to mapP)
open import Relation.Binary.PropositionalEquality
open import Data.Fin


map-∈ : ∀ {a b} {A : Set a} {B : Set b} {y : B} {f : A → B} {n} {xs : Vec A n} → y ∈ map f xs → ∃ λ x → f x ≡ y
map-∈ {xs = []} ()
map-∈ {xs = x ∷ xs} here = x , refl
map-∈ {xs = x ∷ xs} (there y∈mapfxs) = map-∈ y∈mapfxs

∈-map₂ : ∀ {a b} {A : Set a} {B : Set b} {m n : ℕ}
             → ∀ {c} {F : Set c} (f : A → B → F)
             {xs : Vec A m} {ys : Vec B n}
             {x y} → x ∈ xs → y ∈ ys → (f x y) ∈ map₂ f xs ys
∈-map₂ f {xs = x ∷ xs} {ys} here         y∈ys =
  ∈-++ₗ (∈-map (f x) y∈ys)
∈-map₂ f {xs = x ∷ xs} {ys} (there x∈xs) y∈ys =
  ∈-++ᵣ (map (f x) ys) (∈-map₂ f x∈xs y∈ys)

lookup-delete-thin : ∀ {a n} {A : Set a} (x : Fin (suc n)) (y : Fin n) (v : Vec A (suc n)) →
                     lookup y (delete x v) ≡ lookup (thin x y) v
lookup-delete-thin zero zero (_ ∷ _) = refl
lookup-delete-thin zero (suc _) (_ ∷ _) = refl
lookup-delete-thin (suc _) zero (_ ∷ _) = refl
lookup-delete-thin (suc x) (suc y) (_ ∷ v) = lookup-delete-thin x y v
