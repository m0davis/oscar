module Bradley where
  open import Data.Nat
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Relation.Nullary.Decidable
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Function
  open ≡-Reasoning
  open import Data.Nat.Properties.Simple

  _<?_ : Decidable _<_
  m <? n = suc m ≤? n

  data DivMod (m n : ℕ) {_ : False (n ≟ 0)} : Set where
    quotrem : ∀ (q r : ℕ) → r < n → m ≡ q * n + r → DivMod m n

  xrefl : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
  xrefl x = refl

  ≤→≮→≡ : ∀ {a b} → a ≤ b → a ≮ b → a ≡ b
  ≤→≮→≡ {zero}  {zero}  _       _ = refl
  ≤→≮→≡ {zero}  {suc _} _       q = contradiction (s≤s z≤n) q 
  ≤→≮→≡ {suc _} {zero}  ()

  ≤→≮→≡ {suc a} {suc b} (s≤s p) q = cong suc (≤→≮→≡ p (q ∘ s≤s))

  divMod : ∀ (m n : ℕ) {nz : False (n ≟ 0)} → DivMod m n {nz}
  divMod _         zero {}
  divMod zero      (suc n-1) = quotrem zero zero (s≤s z≤n) refl
  divMod (suc m-1) (suc n-1) with divMod m-1 (suc n-1)
  ... | quotrem q r lt eq with r <? n-1
  ...   | yes x = quotrem q (suc r) (s≤s x) $ begin
                    suc m-1
                      ≡⟨ cong suc eq ⟩
                    suc (q * suc n-1 + r)
                      ≡⟨ sym (+-suc (q * suc n-1) r) ⟩
                    q * suc n-1 + suc r ∎
  ...   | no ¬x = quotrem (suc q) zero (s≤s z≤n) $ cong suc $ begin
                    m-1
                      ≡⟨ eq ⟩
                    q * suc n-1 + r
                      ≡⟨ cong₂ _+_ (xrefl (q * suc n-1)) (≤→≮→≡ (≤-pred lt) ¬x) ⟩
                    q * suc n-1 + n-1
                      ≡⟨ +-comm (q * suc n-1) n-1 ⟩
                    n-1 + q * suc n-1
                      ≡⟨ +-comm 0 (n-1 + q * suc n-1) ⟩
                    n-1 + q * suc n-1 + zero ∎
