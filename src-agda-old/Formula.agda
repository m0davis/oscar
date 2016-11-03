module Formula where

open import Level
open import Data.List

data Free {𝑨} (F : Set 𝑨 → Set 𝑨) (A : Set 𝑨) : Set (suc 𝑨) where
  pure : A → Free F A
  free : ∀ {𝑎 : Set 𝑨} → (𝑎 → Free F A) → F 𝑎 → Free F A

-- data Formula {v c} (V : Set v) (C : Set c) : Set (v ⊔ c) where
--   variable : V → Formula V C
--   constant : C → Formula V C
--   formula : C → List (Formula V C) → Formula V C
